import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Constitutive potential and equilibrium curvature floor

Scalar identities for
`V(w) = 3(w-1)² + 3 w⁻²`, with `h(w) = V''(w) + 2 V'(w)/w`.
The global floor is `18 - 9 · 2⁻¹/³`.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Real

/-- Constitutive potential `V(w) = 3(w-1)² + 3 w⁻²`. -/
def V (w : ℝ) : ℝ :=
  3 * (w - 1) ^ 2 + 3 * w ^ (-2 : ℤ)

/-- First derivative `V'(w) = 6(w-1) - 6 w⁻³`. -/
def V' (w : ℝ) : ℝ :=
  6 * (w - 1) - 6 * w ^ (-3 : ℤ)

/-- Second derivative `V''(w) = 6 + 18 w⁻⁴`. -/
def V'' (w : ℝ) : ℝ :=
  6 + 18 * w ^ (-4 : ℤ)

/-- Equilibrium curvature `h(w) = 18 - 12/w + 6/w⁴`. -/
def h (w : ℝ) : ℝ :=
  18 - 12 / w + 6 / w ^ 4

/-- Exact floor `18 - 9 · 2⁻¹/³`. -/
def universalFloor : ℝ :=
  18 - 9 * (2 : ℝ) ^ (-(1 / 3 : ℝ))

/-- Critical conductance `w = 2¹ᐟ³`. -/
def wCrit : ℝ :=
  (2 : ℝ) ^ (1 / 3 : ℝ)

lemma V''_eq_div (w : ℝ) (hw : w ≠ 0) :
    V'' w = 6 + 18 / w ^ 4 := by
  unfold V''
  rw [_root_.zpow_neg, zpow_ofNat]
  field_simp [hw]

lemma h_eq_V''_add_two_V'_div_w (w : ℝ) (hw : w ≠ 0) :
    V'' w + 2 * V' w / w = h w := by
  unfold V'' V' h
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_ofNat, zpow_ofNat]
  field_simp [hw]
  ring

lemma two_neg_third_cubed :
    ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = (1 : ℝ) / 2 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul h2]
  norm_num

lemma two_neg_third_pos : 0 < (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma h_square_identity (w r : ℝ) (hr3 : r ^ 3 = 1 / 2) :
    3 * r * w ^ 4 - 4 * w ^ 3 + 2 =
      2 * (w * r - 1) ^ 2 * (3 * (w * r) ^ 2 + 2 * (w * r) + 1) := by
  have hr4 : r ^ 4 = r / 2 := by
    have : r ^ 4 = r * r ^ 3 := by ring
    rw [this, hr3]
    ring
  ring_nf
  rw [hr3, hr4]
  ring

lemma h_square_nonneg (w r : ℝ) (hr3 : r ^ 3 = 1 / 2) :
    0 ≤ 3 * r * w ^ 4 - 4 * w ^ 3 + 2 := by
  rw [h_square_identity w r hr3]
  have hq : 0 ≤ 3 * (w * r) ^ 2 + 2 * (w * r) + 1 := by
    nlinarith [sq_nonneg (w * r + 1 / 3)]
  positivity

theorem wCrit_pos : 0 < wCrit :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem h_at_wCrit : h wCrit = universalFloor := by
  unfold h wCrit universalFloor
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpow4 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 4 = 2 * (2 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h2)]
    have : (1 / 3 : ℝ) * (4 : ℕ) = 1 + 1 / 3 := by norm_num
    rw [this, Real.rpow_add h2, Real.rpow_one]
  have hinv : ((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹ = (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
    (Real.rpow_neg (le_of_lt h2) (1 / 3 : ℝ)).symm
  rw [hpow4]
  have hrw : 6 / (2 * (2 : ℝ) ^ (1 / 3 : ℝ)) = 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have : 6 / (2 * (2 : ℝ) ^ (1 / 3 : ℝ)) = 3 * ((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
      field_simp
      ring
    rw [this, hinv]
  rw [hrw]
  have hrw12 : 12 / (2 : ℝ) ^ (1 / 3 : ℝ) = 12 * (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [div_eq_mul_inv, hinv]
  rw [hrw12]
  ring

theorem universalFloor_gt_ten : (10 : ℝ) < universalFloor := by
  unfold universalFloor
  set r := (2 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr3 : r ^ 3 = 1 / 2 := two_neg_third_cubed
  have hcube : ((8 : ℝ) / 9) ^ 3 = 512 / 729 := by norm_num
  have hcmp : (512 : ℝ) / 729 > 1 / 2 := by norm_num
  have hmono := Odd.strictMono_pow (R := ℝ) (n := 3) (by decide)
  have : (8 : ℝ) / 9 > r := by
    have : ((8 : ℝ) / 9) ^ 3 > r ^ 3 := by
      rw [hcube, hr3]
      exact hcmp
    exact hmono.lt_iff_lt.mp this
  linarith

theorem universalFloor_pos : 0 < universalFloor :=
  lt_trans (by norm_num : (0 : ℝ) < 10) universalFloor_gt_ten

/-- **LAW.** For every `w > 0`, `h(w) ≥ 18 - 9 · 2⁻¹/³`. -/
theorem h_ge_floor {w : ℝ} (hw : 0 < w) : universalFloor ≤ h w := by
  set r := (2 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr3 : r ^ 3 = 1 / 2 := two_neg_third_cubed
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hdiff : h w - universalFloor = -12 / w + 6 / w ^ 4 + 9 * r := by
    unfold h universalFloor
    ring
  have hmul :
      w ^ 4 * (h w - universalFloor) = 3 * (3 * r * w ^ 4 - 4 * w ^ 3 + 2) := by
    rw [hdiff]
    field_simp [hw0]
    ring
  have hpoly := h_square_nonneg w r hr3
  have hw4 : 0 < w ^ 4 := pow_pos hw 4
  have : 0 ≤ w ^ 4 * (h w - universalFloor) := by
    rw [hmul]
    nlinarith
  have : 0 ≤ h w - universalFloor :=
    (mul_nonneg_iff_of_pos_left hw4).mp this
  linarith

theorem V_ge_three_inv_sq {w : ℝ} (hw : 0 < w) : 3 / w ^ 2 ≤ V w := by
  unfold V
  have hinv : 3 * w ^ (-2 : ℤ) = 3 / w ^ 2 := by
    rw [_root_.zpow_neg, zpow_ofNat]
    field_simp [ne_of_gt hw]
  rw [hinv]
  nlinarith [sq_nonneg (w - 1)]

theorem V''_pos {w : ℝ} (hw : 0 < w) : 0 < V'' w := by
  rw [V''_eq_div w (ne_of_gt hw)]
  have : 0 < w ^ 4 := pow_pos hw 4
  positivity

theorem V'_le_neg_six_div_cube {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    V' w ≤ -6 / w ^ 3 := by
  have hlin : 6 * (w - 1) ≤ 0 := by nlinarith [hw1]
  have hz : w ^ (-3 : ℤ) = 1 / w ^ 3 := by
    rw [_root_.zpow_neg, zpow_ofNat]
    field_simp [ne_of_gt hw]
  have hform : V' w = 6 * (w - 1) - 6 / w ^ 3 := by
    unfold V'
    rw [hz]
    ring
  rw [hform]
  have h := sub_le_sub_right hlin (6 / w ^ 3)
  have hz0 : (0 : ℝ) - 6 / w ^ 3 = -6 / w ^ 3 := by ring
  rwa [hz0] at h

theorem V'_ge_linear {w : ℝ} (hw1 : 1 ≤ w) : 6 * w - 12 ≤ V' w := by
  have hw : 0 < w := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw1
  have hz : w ^ (-3 : ℤ) = 1 / w ^ 3 := by
    rw [_root_.zpow_neg, zpow_ofNat]
    field_simp [ne_of_gt hw]
  have hform : V' w = 6 * (w - 1) - 6 / w ^ 3 := by
    unfold V'
    rw [hz]
    ring
  have hinv : 1 / w ^ 3 ≤ 1 := by
    rw [div_le_one (pow_pos hw 3)]
    have : (1 : ℝ) ^ 3 ≤ w ^ 3 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hw1 3
    simpa using this
  have h6 : 6 / w ^ 3 ≤ 6 := by
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 6)
    simpa [div_eq_mul_inv] using this
  have hsub : 6 * (w - 1) - 6 ≤ 6 * (w - 1) - 6 / w ^ 3 :=
    sub_le_sub_left h6 (6 * (w - 1))
  have hlin : 6 * w - 12 = 6 * (w - 1) - 6 := by ring
  rw [hform, hlin]
  exact hsub

theorem V''_le_1464_of_adm {w : ℝ} (hw : 1 / 3 ≤ w) :
    V'' w ≤ 1464 := by
  have hwpos : 0 < w := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hw
  rw [V''_eq_div w (ne_of_gt hwpos)]
  have hw4 : 0 < w ^ 4 := pow_pos hwpos 4
  have hmono : (1 / 3 : ℝ) ^ 4 ≤ w ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hw 4
  have hinv : 1 / w ^ 4 ≤ 1 / (1 / 3 : ℝ) ^ 4 :=
    one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 3) 4) hmono
  have : (1 / 3 : ℝ) ^ 4 = 1 / 81 := by norm_num
  have : 1 / (1 / 3 : ℝ) ^ 4 = 81 := by norm_num
  have : 18 / w ^ 4 ≤ 18 * 81 := by
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 18)
    have h81 : 18 * (1 / w ^ 4) = 18 / w ^ 4 := by ring
    have hr : 18 * (1 / (1 / 3 : ℝ) ^ 4) = 18 * 81 := by norm_num
    linarith
  linarith

end UniversalStability
