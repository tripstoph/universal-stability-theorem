import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

import UniversalStability.Increment3_SteinLyapunov
import UniversalStability.Increment4_NonlinearEllipsoid

/-!
# Increment (vii) — Euclidean comparison, kinematic lift, quadratic margin

The manuscript's `‖·‖` on `ℝ^n` is Euclidean. The Pi type `ι → ℝ` carries the
sup-norm, so Theorem 5 works with `euc x := √(xᵀx)` and the L2 operator
norm on matrices.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- Euclidean squared length `xᵀx`. -/
def eucSq (x : ι → ℝ) : ℝ := x ⬝ᵥ x

/-- Euclidean length `√(xᵀx)`. -/
def euc (x : ι → ℝ) : ℝ := Real.sqrt (eucSq x)

theorem eucSq_eq_sum (x : ι → ℝ) : eucSq x = ∑ i, x i ^ 2 := by
  simp [eucSq, dotProduct, pow_two]

theorem eucSq_nonneg (x : ι → ℝ) : 0 ≤ eucSq x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem euc_nonneg (x : ι → ℝ) : 0 ≤ euc x :=
  Real.sqrt_nonneg _

theorem euc_eq_toLp (x : ι → ℝ) : euc x = ‖WithLp.toLp 2 x‖ := by
  rw [euc, EuclideanSpace.norm_eq, eucSq_eq_sum]
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

theorem eucSq_eq_toLp_sq (x : ι → ℝ) : eucSq x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [← euc_eq_toLp, euc, Real.sq_sqrt (eucSq_nonneg x)]

theorem toLp_smul (c : ℝ) (x : ι → ℝ) :
    WithLp.toLp 2 (c • x) = c • WithLp.toLp 2 x := by
  ext i
  simp [Pi.smul_apply]

theorem toLp_add (x y : ι → ℝ) :
    WithLp.toLp 2 (x + y) = WithLp.toLp 2 x + WithLp.toLp 2 y := by
  ext i
  simp [Pi.add_apply]

theorem euc_smul (c : ℝ) (x : ι → ℝ) : euc (c • x) = |c| * euc x := by
  rw [euc_eq_toLp, toLp_smul, norm_smul, Real.norm_eq_abs, euc_eq_toLp]

theorem euc_zero : euc (0 : ι → ℝ) = 0 := by
  simp [euc, eucSq]

theorem euc_triangle (x y : ι → ℝ) : euc (x + y) ≤ euc x + euc y := by
  rw [euc_eq_toLp, toLp_add, euc_eq_toLp, euc_eq_toLp]
  exact norm_add_le _ _

theorem abs_dotProduct_le_euc (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ euc x * euc y := by
  have hinner :
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = y ⬝ᵥ x := by
    simpa [star_trivial] using
      EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) x y
  have h := abs_real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [hinner] at h
  rw [dotProduct_comm x y, euc_eq_toLp, euc_eq_toLp]
  exact h

theorem euc_pi_norm_le [Nonempty ι] (x : ι → ℝ) : ‖x‖ ≤ euc x := by
  refine (pi_norm_le_iff_of_nonneg (euc_nonneg x)).2 fun i => ?_
  have hi : |x i| ^ 2 ≤ eucSq x := by
    have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    simpa [eucSq_eq_sum, pow_two, sq_abs] using this
  have : |x i| ≤ Real.sqrt (eucSq x) :=
    (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      (by simpa [Real.sq_sqrt (eucSq_nonneg x)] using hi)
  simpa [Real.norm_eq_abs, euc] using this

theorem euc_le_sqrt_card_mul_pi_norm (x : ι → ℝ) :
    euc x ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ := by
  have hsum : ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using
        (pi_norm_le_iff_of_nonneg (norm_nonneg x)).1 le_rfl i
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hcard : ∑ _i : ι, ‖x‖ ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [euc, eucSq_eq_sum]
  refine (Real.sqrt_le_sqrt (hsum.trans_eq hcard)).trans_eq ?_
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem eucSq_sumElim {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) :
    eucSq (Sum.elim a b) = eucSq a + eucSq b := by
  simp [eucSq_eq_sum, Fintype.sum_sum_type, Sum.elim]

theorem euc_sumElim {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) :
    euc (Sum.elim a b) =
      Real.sqrt (euc a ^ 2 + euc b ^ 2) := by
  have ha := eucSq_nonneg a
  have hb := eucSq_nonneg b
  rw [euc, eucSq_sumElim, euc, euc, Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem euc_sumElim_zero {α β : Type*} [Fintype α] [Fintype β] (b : β → ℝ) :
    euc (Sum.elim (0 : α → ℝ) b) = euc b := by
  rw [euc_sumElim, euc_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.sqrt_sq (euc_nonneg b)]

/-- Euclidean kinematic bound: `‖δw + ΔT v‖₂ ≤ √(1+ΔT²) ‖z‖₂`. -/
theorem euc_kinematic {E : Type*} [Fintype E] (δw v : E → ℝ) (ΔT : ℝ) :
    euc (δw + ΔT • v) ≤
      Real.sqrt (1 + ΔT ^ 2) * euc (Sum.elim δw v) := by
  have htri : euc (δw + ΔT • v) ≤ euc δw + euc (ΔT • v) := euc_triangle _ _
  have hsmul : euc (ΔT • v) = |ΔT| * euc v := euc_smul ΔT v
  have hsplit : eucSq (Sum.elim δw v) = euc δw ^ 2 + euc v ^ 2 := by
    rw [eucSq_sumElim, euc, euc, Real.sq_sqrt (eucSq_nonneg δw),
      Real.sq_sqrt (eucSq_nonneg v)]
  have hsq :
      (euc δw + |ΔT| * euc v) ^ 2 ≤
        (1 + ΔT ^ 2) * eucSq (Sum.elim δw v) := by
    have hcs := two_mul_le_weighted_sq (euc δw) (euc v) ΔT
    rw [hsplit]
    nlinarith [sq_nonneg (euc δw), sq_nonneg (euc v), sq_nonneg ΔT, sq_abs ΔT]
  have hnn : 0 ≤ euc δw + |ΔT| * euc v :=
    add_nonneg (euc_nonneg _) (mul_nonneg (abs_nonneg _) (euc_nonneg _))
  have hnn' : 0 ≤ Real.sqrt (1 + ΔT ^ 2) * euc (Sum.elim δw v) :=
    mul_nonneg (Real.sqrt_nonneg _) (euc_nonneg _)
  have hle :
      euc δw + |ΔT| * euc v ≤
        Real.sqrt (1 + ΔT ^ 2) * euc (Sum.elim δw v) := by
    refine le_of_sq_le_sq ?_ hnn'
    have helim : euc (Sum.elim δw v) ^ 2 = eucSq (Sum.elim δw v) :=
      Real.sq_sqrt (eucSq_nonneg _)
    rw [mul_pow, Real.sq_sqrt (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)),
      helim]
    exact hsq
  refine le_trans htri ?_
  rwa [hsmul]

theorem mulVec_euc_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    euc (A.mulVec x) ≤ ‖A‖ * euc x := by
  have := (toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm (WithLp.toLp 2 x)
  simpa [euc_eq_toLp, toEuclideanCLM_toLp, l2_opNorm_toEuclideanCLM] using this

/-- Lyapunov form `𝒱(z) = zᵀ P z`. -/
def lyap {n : Type*} [Fintype n] (P : Matrix n n ℝ) (z : n → ℝ) : ℝ :=
  z ⬝ᵥ P.mulVec z

theorem lyap_add {n : Type*} [Fintype n]
    {P : Matrix n n ℝ} (hP : Pᵀ = P) (x y : n → ℝ) :
    lyap P (x + y) = lyap P x + lyap P y + 2 * (x ⬝ᵥ P.mulVec y) := by
  have hyx : y ⬝ᵥ P.mulVec x = x ⬝ᵥ P.mulVec y := by
    rw [dotProduct_mulVec y P x, ← mulVec_transpose P y, dotProduct_comm, hP]
  unfold lyap
  rw [mulVec_add]
  rw [dotProduct_add]
  rw [add_dotProduct, add_dotProduct, hyx]
  ring

theorem stein_lyap_contraction {n : Type*} [Fintype n] [DecidableEq n]
    {A P : Matrix n n ℝ} (h : Aᵀ * P * A - P = -1) (z : n → ℝ) :
    lyap P (A.mulVec z) = lyap P z - eucSq z := by
  have hx :
      (A.mulVec z) ⬝ᵥ P.mulVec (A.mulVec z) =
        z ⬝ᵥ Aᵀ.mulVec (P.mulVec (A.mulVec z)) := by
    rw [dotProduct_comm (A.mulVec z), dotProduct_mulVec, ← mulVec_transpose,
      dotProduct_comm]
  have hassoc :
      Aᵀ.mulVec (P.mulVec (A.mulVec z)) = (Aᵀ * P * A).mulVec z := by
    simp [mulVec_mulVec, Matrix.mul_assoc]
  have heq : Aᵀ * P * A = P + (-1 : Matrix n n ℝ) := by
    have h' := eq_add_of_sub_eq h
    rwa [add_comm] at h'
  unfold lyap
  rw [hx, hassoc, heq, add_mulVec, dotProduct_add]
  have hneg : ((-1 : Matrix n n ℝ).mulVec z) = -z := by
    simp [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hneg, dotProduct_neg]
  rfl

theorem lyap_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (z : n → ℝ) :
    lyap P z ≤ ‖P‖ * eucSq z := by
  have habs : |z ⬝ᵥ P.mulVec z| ≤ euc z * euc (P.mulVec z) :=
    abs_dotProduct_le_euc z (P.mulVec z)
  have hop : euc (P.mulVec z) ≤ ‖P‖ * euc z := mulVec_euc_le P z
  have hle : lyap P z ≤ euc z * euc (P.mulVec z) := (abs_le.mp habs).2
  have hmul : euc z * euc (P.mulVec z) ≤ euc z * (‖P‖ * euc z) :=
    mul_le_mul_of_nonneg_left hop (euc_nonneg z)
  have hsqz : euc z * euc z = eucSq z := by
    rw [← pow_two, euc, Real.sq_sqrt (eucSq_nonneg z)]
  have hrew : euc z * (‖P‖ * euc z) = ‖P‖ * eucSq z := by
    calc
      euc z * (‖P‖ * euc z) = ‖P‖ * (euc z * euc z) := by ring
      _ = ‖P‖ * eucSq z := by rw [hsqz]
  exact hle.trans (hmul.trans_eq hrew)

theorem eucSq_single_one {n : Type*} [Fintype n] [DecidableEq n] (i : n) :
    eucSq (Pi.single i (1 : ℝ)) = 1 := by
  rw [eucSq_eq_sum]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
  · simp [Pi.single_eq_same]

theorem one_le_opNorm_of_quad_floor {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {P : Matrix n n ℝ}
    (hfloor : ∀ x : n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ P.mulVec x) :
    1 ≤ ‖P‖ := by
  obtain ⟨i⟩ := ‹Nonempty n›
  set x : n → ℝ := Pi.single i (1 : ℝ)
  have heuc : eucSq x = 1 := eucSq_single_one i
  have hV : 1 ≤ lyap P x := by
    unfold lyap
    have hx1 : x ⬝ᵥ x = 1 := heuc
    have := hfloor x
    rwa [hx1] at this
  have hle : lyap P x ≤ ‖P‖ * eucSq x := lyap_le_opNorm P x
  nlinarith [norm_nonneg P]

/-- Continuity of `1 − a t − b t²` at `0` yields a margin `≥ 1/2` on a
positive interval. Avoids quantifier elimination: on `[0, δ]` one has
`t² ≤ t`, so the quadratic is dominated by a linear term. -/
theorem quadratic_margin_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ δstar, 0 < δstar ∧ ∀ t : ℝ, 0 ≤ t → t ≤ δstar →
      (1 / 2 : ℝ) ≤ 1 - a * t - b * t ^ 2 := by
  let den := 2 * (a + b) + 1
  have hden : 0 < den := by
    have : 0 ≤ 2 * (a + b) := mul_nonneg (by norm_num) (add_nonneg ha hb)
    linarith
  refine ⟨den⁻¹, inv_pos.mpr hden, ?_⟩
  intro t ht0 ht
  have ht1 : t ≤ 1 := by
    have hden1 : (1 : ℝ) ≤ den := by
      have : 0 ≤ 2 * (a + b) := mul_nonneg (by norm_num) (add_nonneg ha hb)
      linarith
    exact ht.trans (inv_le_one_of_one_le₀ hden1)
  have htsq : t ^ 2 ≤ t := by nlinarith
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hlin : a * t + b * t ^ 2 ≤ (a + b) * t := by nlinarith
  have hfrac : (a + b) * t ≤ (a + b) * den⁻¹ :=
    mul_le_mul_of_nonneg_left ht hab
  have hhalf : (a + b) * den⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    unfold den
    linarith
  linarith

end UniversalStability
