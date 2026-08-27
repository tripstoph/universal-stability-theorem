import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Increment (iv) — kinematic bound

`‖δw + ΔT v‖ ≤ √(1+ΔT²) √(‖δw‖²+‖v‖²)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem two_mul_le_weighted_sq (a b ΔT : ℝ) :
    2 * |ΔT| * a * b ≤ ΔT ^ 2 * a ^ 2 + b ^ 2 := by
  have := sq_nonneg (|ΔT| * a - b)
  nlinarith [sq_abs ΔT]

theorem kinematic_next_le (δw v : E) (ΔT : ℝ) :
    ‖δw + ΔT • v‖ ≤ Real.sqrt (1 + ΔT ^ 2) * Real.sqrt (‖δw‖ ^ 2 + ‖v‖ ^ 2) := by
  have htri : ‖δw + ΔT • v‖ ≤ ‖δw‖ + ‖ΔT • v‖ := norm_add_le _ _
  have hsmul : ‖ΔT • v‖ = |ΔT| * ‖v‖ := norm_smul ΔT v
  have hsq :
      (‖δw‖ + |ΔT| * ‖v‖) ^ 2 ≤ (1 + ΔT ^ 2) * (‖δw‖ ^ 2 + ‖v‖ ^ 2) := by
    have hcs := two_mul_le_weighted_sq ‖δw‖ ‖v‖ ΔT
    nlinarith [sq_nonneg ‖δw‖, sq_nonneg ‖v‖, sq_nonneg ΔT, sq_abs ΔT]
  have hnn : 0 ≤ ‖δw‖ + |ΔT| * ‖v‖ := add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hnn' : 0 ≤ Real.sqrt (1 + ΔT ^ 2) * Real.sqrt (‖δw‖ ^ 2 + ‖v‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hle :
      ‖δw‖ + |ΔT| * ‖v‖ ≤
        Real.sqrt (1 + ΔT ^ 2) * Real.sqrt (‖δw‖ ^ 2 + ‖v‖ ^ 2) := by
    refine le_of_sq_le_sq ?_ hnn'
    rw [mul_pow, Real.sq_sqrt (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)),
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hsq
  refine le_trans htri ?_
  rwa [hsmul]

end UniversalStability
