import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

import UniversalStability.Constitutive
import UniversalStability.Force
import UniversalStability.Theorem2

/-!
# Theorem 3 — linearized discrete stability

The 2×2 block is `J_eig = [[1, ΔT], [-ΔT eig, 1 - γ ΔT - eig ΔT²]]` with `γ = 3`.
Jury: `|1-γΔT|<1`, `eig(ΔT)²>0`, `4-2γΔT-eig(ΔT)²>0`.
On `0 < eig ≤ 1464` this holds for `0 < ΔT < (-3 + √5865)/1464`.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Matrix

def modeBlock (γ ΔT eig : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, ΔT; -ΔT * eig, 1 - γ * ΔT - eig * ΔT ^ 2]

theorem modeBlock_det (γ ΔT eig : ℝ) :
    (modeBlock γ ΔT eig).det = 1 - γ * ΔT := by
  simp [modeBlock, Matrix.det_fin_two]
  ring

theorem modeBlock_trace (γ ΔT eig : ℝ) :
    (modeBlock γ ΔT eig).trace = 2 - γ * ΔT - eig * ΔT ^ 2 := by
  simp [modeBlock, Matrix.trace_fin_two]
  ring

def JuryStable (γ ΔT eig : ℝ) : Prop :=
  |1 - γ * ΔT| < 1 ∧ 0 < eig * ΔT ^ 2 ∧ 0 < 4 - 2 * γ * ΔT - eig * ΔT ^ 2

/-- Product of roots of `μ² - τμ + δ = 0` is `δ = 1 - γ ΔT`.
When the discriminant is negative the roots are conjugates and `|μ|² = δ`. -/
theorem modeBlock_root_product (γ ΔT eig : ℝ) :
    (modeBlock γ ΔT eig).det = 1 - γ * ΔT :=
  modeBlock_det γ ΔT eig

def deltaTStar : ℝ :=
  (-3 + Real.sqrt 5865) / 1464

theorem quadratic_at_pos_root (γ eig : ℝ) (heig : 0 < eig)
    (hdisc : 0 ≤ γ ^ 2 + 4 * eig) :
    eig * ((-γ + Real.sqrt (γ ^ 2 + 4 * eig)) / eig) ^ 2 +
      2 * γ * ((-γ + Real.sqrt (γ ^ 2 + 4 * eig)) / eig) - 4 = 0 := by
  set s := Real.sqrt (γ ^ 2 + 4 * eig)
  have hs : s ^ 2 = γ ^ 2 + 4 * eig := Real.sq_sqrt hdisc
  have hlam : eig ≠ 0 := ne_of_gt heig
  have hsplit :
      eig * ((-γ + s) / eig) ^ 2 + 2 * γ * ((-γ + s) / eig) - 4 =
        ((-γ + s) ^ 2 + 2 * γ * (-γ + s) - 4 * eig) / eig := by
    field_simp [hlam]
  have hnum : (-γ + s) ^ 2 + 2 * γ * (-γ + s) - 4 * eig = 0 := by
    nlinarith [hs]
  rw [hsplit, hnum, zero_div]

/-- For `γ ≥ 0`, `eig > 0`, the quadratic `eig t² + 2γ t - 4` is increasing on
`[0, ∞)` and vanishes at the positive root, hence is negative on `(0, r₊)`. -/
theorem jury_high_freq (γ ΔT eig : ℝ) (hγ : 0 ≤ γ) (heig : 0 < eig) (hΔT : 0 < ΔT)
    (h : ΔT < (-γ + Real.sqrt (γ ^ 2 + 4 * eig)) / eig) :
    0 < 4 - 2 * γ * ΔT - eig * ΔT ^ 2 := by
  have hdisc : 0 ≤ γ ^ 2 + 4 * eig := by nlinarith [sq_nonneg γ]
  set r := (-γ + Real.sqrt (γ ^ 2 + 4 * eig)) / eig
  have hat : eig * r ^ 2 + 2 * γ * r - 4 = 0 := by
    simpa [r] using quadratic_at_pos_root γ eig heig hdisc
  have hinc : eig * ΔT ^ 2 + 2 * γ * ΔT - 4 < eig * r ^ 2 + 2 * γ * r - 4 := by
    have : eig * r ^ 2 + 2 * γ * r - 4 - (eig * ΔT ^ 2 + 2 * γ * ΔT - 4) =
        (r - ΔT) * (eig * (r + ΔT) + 2 * γ) := by ring
    have hrΔ : 0 < r - ΔT := sub_pos.mpr h
    have hsum : 0 < eig * (r + ΔT) + 2 * γ := by
      have : 0 < r + ΔT := by
        have hrpos : 0 < r := lt_trans hΔT h
        linarith
      nlinarith
    nlinarith
  have hq : eig * ΔT ^ 2 + 2 * γ * ΔT - 4 < 0 := by linarith [hat]
  linarith

theorem det_condition {ΔT : ℝ} (h : 0 < ΔT) (h2 : ΔT < 2 / 3) :
    |(1 : ℝ) - 3 * ΔT| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

theorem deltaTStar_lt_two_thirds : deltaTStar < 2 / 3 := by
  unfold deltaTStar
  have hsq : Real.sqrt 5865 < 77 := by
    refine (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 77)).mpr ?_
    norm_num
  have : -3 + Real.sqrt 5865 < 74 := by linarith
  have : (-3 + Real.sqrt 5865) / 1464 < 74 / 1464 :=
    div_lt_div_of_pos_right this (by norm_num)
  have : (74 : ℝ) / 1464 < 2 / 3 := by norm_num
  linarith

theorem deltaTStar_pos : 0 < deltaTStar := by
  unfold deltaTStar
  have : (3 : ℝ) ^ 2 < 5865 := by norm_num
  have hsq : 3 < Real.sqrt 5865 := by
    refine (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 3)).mpr ?_
    norm_num
  have : 0 < -3 + Real.sqrt 5865 := by linarith
  exact div_pos this (by norm_num)

/-- **Theorem 3.** `γ = 3`, `0 < eig ≤ 1464`, `0 < ΔT < (-3+√5865)/1464`
implies the three Jury inequalities. -/
theorem theorem3_jury (eig ΔT : ℝ) (heig0 : 0 < eig) (heig : eig ≤ 1464)
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    JuryStable 3 ΔT eig := by
  refine ⟨?_, ?_, ?_⟩
  · exact det_condition hΔT (lt_trans hstep deltaTStar_lt_two_thirds)
  · exact mul_pos heig0 (sq_pos_of_pos hΔT)
  · -- 4 - 6 ΔT - eig ΔT² ≥ 4 - 6 ΔT - 1464 ΔT² > 0
    have h1464 : 0 < 4 - 2 * (3 : ℝ) * ΔT - 1464 * ΔT ^ 2 := by
      have hroot : deltaTStar = (-(3 : ℝ) + Real.sqrt (3 ^ 2 + 4 * 1464)) / 1464 := by
        unfold deltaTStar
        norm_num
      rw [hroot] at hstep
      simpa using
        jury_high_freq (γ := 3) (ΔT := ΔT) (eig := 1464) (by norm_num)
          (by norm_num) hΔT hstep
    have : 4 - 2 * (3 : ℝ) * ΔT - eig * ΔT ^ 2 ≥
        4 - 2 * 3 * ΔT - 1464 * ΔT ^ 2 := by
      have : eig * ΔT ^ 2 ≤ 1464 * ΔT ^ 2 :=
        mul_le_mul_of_nonneg_right heig (sq_nonneg _)
      linarith
    linarith

/-- If `Jᵀ P J - P = -I`, then `𝒱(Jx) = 𝒱(x) - ‖x‖²`. -/
theorem discrete_lyapunov_contraction (J P : Matrix (Fin 2) (Fin 2) ℝ)
    (h : Jᵀ * P * J - P = -1) (x : Fin 2 → ℝ) :
    dotProduct (J.mulVec x) (P.mulVec (J.mulVec x)) =
      dotProduct x (P.mulVec x) - dotProduct x x := by
  have hx :
      dotProduct (J.mulVec x) (P.mulVec (J.mulVec x)) =
        dotProduct x (Jᵀ.mulVec (P.mulVec (J.mulVec x))) := by
    rw [dotProduct_comm (J.mulVec x), dotProduct_mulVec, ← mulVec_transpose,
      dotProduct_comm]
  have hassoc :
      Jᵀ.mulVec (P.mulVec (J.mulVec x)) = (Jᵀ * P * J).mulVec x := by
    simp [mulVec_mulVec, Matrix.mul_assoc]
  have heq : Jᵀ * P * J = P + (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have h' := eq_add_of_sub_eq h
    rwa [add_comm] at h'
  rw [hx, hassoc, heq, add_mulVec, dotProduct_add]
  have hneg : ((-1 : Matrix (Fin 2) (Fin 2) ℝ).mulVec x) = -x := by
    simp [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hneg, dotProduct_neg]
  ring

/-- Underdamped modulus: if the discriminant is negative, the complex
conjugate roots satisfy `|μ|² = det J = 1 - γ ΔT`. -/
theorem underdamped_normSq (γ ΔT eig : ℝ)
    (hdisc : (modeBlock γ ΔT eig).trace ^ 2 < 4 * (modeBlock γ ΔT eig).det) :
    (((modeBlock γ ΔT eig).trace +
        Complex.I * Real.sqrt (4 * (modeBlock γ ΔT eig).det -
          (modeBlock γ ΔT eig).trace ^ 2)) / 2).normSq =
      (modeBlock γ ΔT eig).det := by
  set τ := (modeBlock γ ΔT eig).trace
  set δ := (modeBlock γ ΔT eig).det
  have hpos : 0 < 4 * δ - τ ^ 2 := by linarith
  have hsq : (Real.sqrt (4 * δ - τ ^ 2)) ^ 2 = 4 * δ - τ ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  simp [Complex.normSq, τ, δ]
  field_simp
  nlinarith [hsq]

/-- Specialization `γ = 3`: underdamped `|μ|² = 1 - 3 ΔT`. -/
theorem underdamped_mod_sq_gamma3 (ΔT eig : ℝ)
    (hdisc : (modeBlock 3 ΔT eig).trace ^ 2 < 4 * (modeBlock 3 ΔT eig).det) :
    (((modeBlock 3 ΔT eig).trace +
        Complex.I * Real.sqrt (4 * (modeBlock 3 ΔT eig).det -
          (modeBlock 3 ΔT eig).trace ^ 2)) / 2).normSq =
      1 - 3 * ΔT := by
  have h := underdamped_normSq 3 ΔT eig hdisc
  simpa [modeBlock_det] using h

/-- Jury's 2×2 criterion: `|det|<1` and `|tr|<1+det`, equivalent to the
three inequalities in `JuryStable` when `eig>0` and `ΔT≠0`. -/
theorem juryStable_iff_trace_det (γ ΔT eig : ℝ) (heig : 0 < eig)
    (hΔT : ΔT ≠ 0) :
    JuryStable γ ΔT eig ↔
      |(modeBlock γ ΔT eig).det| < 1 ∧
        |(modeBlock γ ΔT eig).trace| < 1 + (modeBlock γ ΔT eig).det := by
  constructor
  · intro ⟨hdet, hpos, h4⟩
    refine ⟨?_, ?_⟩
    · simpa [modeBlock_det] using hdet
    · rw [abs_lt]
      constructor
      · simp [modeBlock_trace, modeBlock_det]
        linarith
      · simp [modeBlock_trace, modeBlock_det]
        linarith
  · intro ⟨hdet, htr⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [modeBlock_det] using hdet
    · exact mul_pos heig (sq_pos_of_ne_zero hΔT)
    · have hlt := (abs_lt.mp htr).1
      simp [modeBlock_trace, modeBlock_det] at hlt
      linarith

/-- Underdamped `γ=3` modes have `|μ|<1` whenever `ΔT>0`.
(`disc<0` already forces `det = 1-3ΔT > 0`.) -/
theorem underdamped_mod_lt_one (ΔT eig : ℝ) (hΔT : 0 < ΔT)
    (hdisc : (modeBlock 3 ΔT eig).trace ^ 2 < 4 * (modeBlock 3 ΔT eig).det) :
    (((modeBlock 3 ΔT eig).trace +
        Complex.I * Real.sqrt (4 * (modeBlock 3 ΔT eig).det -
          (modeBlock 3 ΔT eig).trace ^ 2)) / 2).normSq < 1 := by
  have hsq := underdamped_mod_sq_gamma3 ΔT eig hdisc
  rw [hsq]
  linarith

/-- A real characteristic root of a Jury-stable block lies in `(-1,1)`. -/
theorem juryStable_real_root_abs_lt_one (γ ΔT eig μ : ℝ)
    (heig : 0 < eig) (hΔT : ΔT ≠ 0) (hJ : JuryStable γ ΔT eig)
    (hroot : μ ^ 2 - (modeBlock γ ΔT eig).trace * μ +
      (modeBlock γ ΔT eig).det = 0) :
    |μ| < 1 := by
  have htd := (juryStable_iff_trace_det γ ΔT eig heig hΔT).mp hJ
  set τ := (modeBlock γ ΔT eig).trace with hτdef
  set δ := (modeBlock γ ΔT eig).det with hδdef
  have hδ : |δ| < 1 := by simpa [hδdef, modeBlock_det] using htd.1
  have hτ : |τ| < 1 + δ := by simpa [hτdef, modeBlock_trace] using htd.2
  have hp1 : 0 < 1 - τ + δ := by
    have := abs_lt.mp hτ
    linarith
  have hpm1 : 0 < 1 + τ + δ := by
    have := abs_lt.mp hτ
    linarith
  have hp1id : 1 - τ + δ = (1 - μ) * (1 + μ - τ) := by
    have : μ ^ 2 = τ * μ - δ := by linarith [hroot]
    nlinarith
  have hpm1id : 1 + τ + δ = (1 + μ) * (1 - μ + τ) := by
    have : μ ^ 2 = τ * μ - δ := by linarith [hroot]
    nlinarith
  by_contra hge
  have h1 : 1 ≤ |μ| := le_of_not_gt hge
  cases le_total μ 0 with
  | inl hnonpos =>
    have : μ ≤ -1 := by
      have : |μ| = -μ := abs_of_nonpos hnonpos
      linarith
    have hμ1 : 1 + μ ≤ 0 := by linarith
    by_cases hlt : μ < -1
    · have hfac : 1 - μ + τ < 0 := by
        have : 0 < (1 + μ) * (1 - μ + τ) := by simpa [hpm1id] using hpm1
        nlinarith
      have hτle : τ ≤ -2 := by linarith
      have habs : 2 ≤ |τ| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have : 1 + δ > 2 := by linarith [abs_lt.mp hτ]
      have hδgt : 1 < |δ| := by
        have : 1 < δ := by linarith
        rwa [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) this)]
      exact (not_le_of_gt hδ) (le_of_lt hδgt)
    · have : μ = -1 := le_antisymm this (le_of_not_gt hlt)
      have : 1 + τ + δ = 0 := by
        rw [this] at hpm1id
        simpa using hpm1id
      linarith
  | inr hnonneg =>
    have : 1 ≤ μ := by
      have : |μ| = μ := abs_of_nonneg hnonneg
      linarith
    by_cases hgt : 1 < μ
    · have hfac : 1 + μ - τ < 0 := by
        have : 0 < (1 - μ) * (1 + μ - τ) := by simpa [hp1id] using hp1
        nlinarith
      have hτge : 2 ≤ τ := by linarith
      have habs : 2 ≤ |τ| := by
        rw [abs_of_nonneg (by linarith)]
        exact hτge
      have : 1 + δ > 2 := by linarith [abs_lt.mp hτ]
      have hδgt : 1 < |δ| := by
        have : 1 < δ := by linarith
        rwa [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) this)]
      exact (not_le_of_gt hδ) (le_of_lt hδgt)
    · have : μ = 1 := le_antisymm (le_of_not_gt hgt) this
      have : 1 - τ + δ = 0 := by
        rw [this] at hp1id
        simpa using hp1id
      linarith

/-- If `P ≻ 0` solves the discrete Lyapunov equation, `𝒱` strictly decreases
off the origin. -/
theorem discrete_lyapunov_posDef_strict (J P : Matrix (Fin 2) (Fin 2) ℝ)
    (_hP : P.PosDef) (h : Jᵀ * P * J - P = -1) {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    dotProduct (J.mulVec x) (P.mulVec (J.mulVec x)) <
      dotProduct x (P.mulVec x) := by
  rw [discrete_lyapunov_contraction J P h x]
  have hx2 : 0 < dotProduct x x := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ x i ^ 2 :=
      fun _ _ => sq_nonneg _
    have hsum : ∑ i, x i ^ 2 = 0 → x = 0 := by
      intro h0
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i (Finset.mem_univ i)
      exact eq_zero_of_pow_eq_zero this
    have hne : dotProduct x x ≠ 0 := by
      intro h0
      exact hx (hsum (by simpa [dotProduct, pow_two] using h0))
    have : 0 ≤ dotProduct x x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    exact lt_of_le_of_ne this hne.symm
  linarith

/-- Rate form: `𝒱(Jx) ≤ (1 - λ_max(P)⁻¹) 𝒱(x)` whenever
`𝒱(y) ≤ λ_max ‖y‖²`. -/
theorem discrete_lyapunov_rate (J P : Matrix (Fin 2) (Fin 2) ℝ)
    (h : Jᵀ * P * J - P = -1) (lamMax : ℝ) (hlam : 0 < lamMax)
    (hRay : ∀ y, dotProduct y (P.mulVec y) ≤ lamMax * dotProduct y y)
    (x : Fin 2 → ℝ) :
    dotProduct (J.mulVec x) (P.mulVec (J.mulVec x)) ≤
      (1 - lamMax⁻¹) * dotProduct x (P.mulVec x) := by
  rw [discrete_lyapunov_contraction J P h x]
  have hV := hRay x
  have hnorm : lamMax⁻¹ * dotProduct x (P.mulVec x) ≤ dotProduct x x := by
    have := mul_le_mul_of_nonneg_left hV (inv_nonneg.mpr (le_of_lt hlam))
    have hcancel : lamMax⁻¹ * (lamMax * dotProduct x x) = dotProduct x x := by
      field_simp [ne_of_gt hlam]
    linarith
  have hdistrib :
      (1 - lamMax⁻¹) * dotProduct x (P.mulVec x) =
        dotProduct x (P.mulVec x) - lamMax⁻¹ * dotProduct x (P.mulVec x) := by
    ring
  linarith [hdistrib, hnorm]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Linearized leapfrog map on `(δw, δv) ∈ ℝ^E ⊕ ℝ^E`. -/
def leapfrogLin (γ ΔT : ℝ) (H : Matrix E E ℝ) :
    Matrix (E ⊕ E) (E ⊕ E) ℝ :=
  Matrix.fromBlocks (1 : Matrix E E ℝ) (ΔT • (1 : Matrix E E ℝ))
    ((-ΔT) • H) ((1 - γ * ΔT) • (1 : Matrix E E ℝ) - ΔT ^ 2 • H)

/-- On an eigenmode `H v = eig • v`, the leapfrog map restricts to `modeBlock`. -/
theorem leapfrogLin_on_eigenmode (γ ΔT eig : ℝ) (H : Matrix E E ℝ)
    (v : E → ℝ) (hv : H.mulVec v = eig • v) (a b : ℝ) :
    (leapfrogLin (E := E) γ ΔT H).mulVec (Sum.elim (a • v) (b • v)) =
      Sum.elim ((a + ΔT * b) • v)
        ((-ΔT * eig * a + (1 - γ * ΔT - eig * ΔT ^ 2) * b) • v) := by
  have hinl : (Sum.elim (a • v) (b • v) ∘ Sum.inl) = a • v := rfl
  have hinr : (Sum.elim (a • v) (b • v) ∘ Sum.inr) = b • v := rfl
  rw [leapfrogLin, Matrix.fromBlocks_mulVec, hinl, hinr]
  have h1w : (1 : Matrix E E ℝ).mulVec (a • v) = a • v := by
    simp [Matrix.one_mulVec]
  have h1v : (1 : Matrix E E ℝ).mulVec (b • v) = b • v := by
    simp [Matrix.one_mulVec]
  have hHw : H.mulVec (a • v) = (a * eig) • v := by
    rw [mulVec_smul, hv, smul_smul, mul_comm]
  have hHv : H.mulVec (b • v) = (b * eig) • v := by
    rw [mulVec_smul, hv, smul_smul, mul_comm]
  have hleft : ((-ΔT) • H).mulVec (a • v) = (-ΔT * a * eig) • v := by
    rw [smul_mulVec, hHw, smul_smul]
    congr 1
    ring
  have hA : ((1 - γ * ΔT) • (1 : Matrix E E ℝ)).mulVec (b • v) =
      ((1 - γ * ΔT) * b) • v := by
    rw [smul_mulVec, h1v, smul_smul]
  have hB : (ΔT ^ 2 • H).mulVec (b • v) = (ΔT ^ 2 * b * eig) • v := by
    rw [smul_mulVec, hHv, smul_smul]
    congr 1
    ring
  have hrest :
      (((1 - γ * ΔT) • (1 : Matrix E E ℝ) - ΔT ^ 2 • H).mulVec (b • v)) =
        ((1 - γ * ΔT) * b - ΔT ^ 2 * b * eig) • v := by
    rw [sub_mulVec, hA, hB, ← sub_smul]
  have hfirst :
      (1 : Matrix E E ℝ).mulVec (a • v) +
          (ΔT • (1 : Matrix E E ℝ)).mulVec (b • v) =
        (a + ΔT * b) • v := by
    rw [h1w, smul_mulVec, h1v, smul_smul, ← add_smul]
  have hsecond :
      ((-ΔT) • H).mulVec (a • v) +
          (((1 - γ * ΔT) • (1 : Matrix E E ℝ) - ΔT ^ 2 • H).mulVec (b • v)) =
        (-ΔT * eig * a + (1 - γ * ΔT - eig * ΔT ^ 2) * b) • v := by
    rw [hleft, hrest, ← add_smul]
    congr 1
    ring
  exact congr_arg₂ Sum.elim hfirst hsecond

/-- Rayleigh form of the manuscript spectral inclusion: at force balance on
the Adm lower bound, `floor ‖x‖² ≤ xᵀ ℋ x ≤ 1464 ‖x‖²`. -/
theorem theorem3_rayleigh_bounds (c : ℝ) (hc : 0 ≤ c)
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V E ℝ) (eta : V → ℝ) (w x : E → ℝ)
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w)) :
    universalFloor * ∑ e, x e ^ 2 ≤
        dotProduct x
          ((onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
              (Bᵀ.mulVec (onShellPotential B eta w))).mulVec x) ∧
      dotProduct x
          ((onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
              (Bᵀ.mulVec (onShellPotential B eta w))).mulVec x) ≤
        1464 * ∑ e, x e ^ 2 := by
  have hw : ∀ e, 0 < w e := fun e =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hadm e)
  refine ⟨?_, hessian_quad_le_1464 c hc B (onShellPotential B eta w) w x hconn hadm⟩
  exact universal_equilibrium_hessian_posdef c hc B eta w hbal hconn hw hF x

/-- Every Rayleigh quotient in `(0, 1464]` is Jury-stable for this paper's step. -/
theorem theorem3_modal_jury (eig ΔT : ℝ) (heig0 : 0 < eig) (heig : eig ≤ 1464)
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    JuryStable 3 ΔT eig :=
  theorem3_jury eig ΔT heig0 heig hΔT hstep

/-- **Theorem 3 (Schur on each block).** Jury-stable modes have every
characteristic root of modulus strictly less than one: real roots lie in
`(-1,1)`, and underdamped roots satisfy `|μ|² = 1-3ΔT < 1`. -/
theorem theorem3_block_schur (eig ΔT : ℝ) (heig0 : 0 < eig) (heig : eig ≤ 1464)
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    JuryStable 3 ΔT eig ∧
      (∀ μ : ℝ, μ ^ 2 - (modeBlock 3 ΔT eig).trace * μ +
          (modeBlock 3 ΔT eig).det = 0 → |μ| < 1) ∧
      ((modeBlock 3 ΔT eig).trace ^ 2 < 4 * (modeBlock 3 ΔT eig).det →
        (((modeBlock 3 ΔT eig).trace +
            Complex.I * Real.sqrt (4 * (modeBlock 3 ΔT eig).det -
              (modeBlock 3 ΔT eig).trace ^ 2)) / 2).normSq < 1) := by
  have hJ := theorem3_jury eig ΔT heig0 heig hΔT hstep
  refine ⟨hJ, ?_, ?_⟩
  · intro μ hroot
    exact juryStable_real_root_abs_lt_one 3 ΔT eig μ heig0 (ne_of_gt hΔT) hJ hroot
  · intro hdisc
    exact underdamped_mod_lt_one ΔT eig hΔT hdisc

end UniversalStability
