import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Orthogonal projectors in Loewner order

If `Pᵀ = P` and `P * P = P`, then `0 ≼ P ≼ I` as quadratic forms:
`0 ≤ xᵀ P x ≤ xᵀ x`.
-/

set_option autoImplicit false

namespace UniversalStability

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetric idempotent matrix (orthogonal projector). -/
def IsOrthogonalProjector (P : Matrix n n ℝ) : Prop :=
  Pᵀ = P ∧ P * P = P

omit [DecidableEq n] in
theorem mulVec_eq_of_idempotent (P : Matrix n n ℝ)
    (hidemp : P * P = P) (x : n → ℝ) :
    P.mulVec (P.mulVec x) = P.mulVec x := by
  rw [mulVec_mulVec, hidemp]

theorem mulVec_remainder_eq_zero (P : Matrix n n ℝ)
    (hidemp : P * P = P) (x : n → ℝ) :
    P.mulVec (x - P.mulVec x) = 0 := by
  rw [mulVec_sub, mulVec_eq_of_idempotent P hidemp, sub_self]

theorem projector_kernel_orthogonal (P : Matrix n n ℝ)
    (hP : IsOrthogonalProjector P) (x : n → ℝ) :
    dotProduct (P.mulVec x) (x - P.mulVec x) = 0 := by
  have hsymm : Pᵀ = P := hP.1
  have hker := mulVec_remainder_eq_zero P hP.2 x
  have hcomm :
      dotProduct (P.mulVec x) (x - P.mulVec x) =
        dotProduct (x - P.mulVec x) (P.mulVec x) :=
    dotProduct_comm _ _
  rw [hcomm, dotProduct_mulVec, ← mulVec_transpose, hsymm, hker,
    dotProduct_comm, dotProduct_zero]

theorem dotProduct_mulVec_eq_of_projector (P : Matrix n n ℝ)
    (hP : IsOrthogonalProjector P) (x : n → ℝ) :
    dotProduct x (P.mulVec x) = dotProduct (P.mulVec x) (P.mulVec x) := by
  have hsplit :
      dotProduct (P.mulVec x) x =
        dotProduct (P.mulVec x) (P.mulVec x) +
          dotProduct (P.mulVec x) (x - P.mulVec x) := by
    have : x = P.mulVec x + (x - P.mulVec x) := by abel
    rw [this, dotProduct_add]
    abel
  rw [dotProduct_comm, hsplit, projector_kernel_orthogonal P hP, add_zero]

theorem projector_remainder_sq (P : Matrix n n ℝ)
    (hP : IsOrthogonalProjector P) (x : n → ℝ) :
    dotProduct (x - P.mulVec x) (x - P.mulVec x) =
      dotProduct x x - dotProduct (P.mulVec x) (P.mulVec x) := by
  have hPx : dotProduct x (P.mulVec x) =
      dotProduct (P.mulVec x) (P.mulVec x) :=
    dotProduct_mulVec_eq_of_projector P hP x
  have hxP : dotProduct (P.mulVec x) x = dotProduct x (P.mulVec x) :=
    dotProduct_comm _ _
  calc
    dotProduct (x - P.mulVec x) (x - P.mulVec x)
        = dotProduct x x - dotProduct x (P.mulVec x) -
            dotProduct (P.mulVec x) x +
              dotProduct (P.mulVec x) (P.mulVec x) := by
          simp [sub_eq_add_neg, dotProduct_add, dotProduct_neg]
          ring
    _ = dotProduct x x - dotProduct (P.mulVec x) (P.mulVec x) := by
          rw [hPx, hxP, hPx]
          ring

/-- **LAW.** An orthogonal projector satisfies `xᵀ P x ≤ xᵀ x`. -/
theorem projector_le_identity (P : Matrix n n ℝ)
    (hP : IsOrthogonalProjector P) (x : n → ℝ) :
    dotProduct x (P.mulVec x) ≤ dotProduct x x := by
  have hdot := dotProduct_mulVec_eq_of_projector P hP x
  have hrem := projector_remainder_sq P hP x
  have hpos : 0 ≤ dotProduct (x - P.mulVec x) (x - P.mulVec x) :=
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rw [hdot]
  linarith [hrem, hpos]

/-- **LAW.** An orthogonal projector satisfies `0 ≤ xᵀ P x`. -/
theorem projector_nonneg (P : Matrix n n ℝ)
    (hP : IsOrthogonalProjector P) (x : n → ℝ) :
    0 ≤ dotProduct x (P.mulVec x) := by
  rw [dotProduct_mulVec_eq_of_projector P hP x]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

end UniversalStability
