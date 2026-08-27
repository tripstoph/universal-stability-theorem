import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

import UniversalStability.Projector
import UniversalStability.ShiftedGreen

/-!
# Loewner bound identified with `W⁻¹ᐟ² Π W⁻¹ᐟ²`

On a connected balanced host with `w > 0`,

  `Π = B̃ᵀ M_w⁻¹ B̃`, `B̃ = B diag(√w)`,

is an orthogonal projector, and `Bᵀ M_w⁻¹ B = W⁻¹ᐟ² Π W⁻¹ᐟ² ≼ W⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Finset Real

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Scaled incidence `B̃ = B diag(√w)`. -/
def scaledInc (B : Matrix V E ℝ) (w : E → ℝ) : Matrix V E ℝ :=
  B * diagonal (fun e => Real.sqrt (w e))

/-- `Π = B̃ᵀ M_w⁻¹ B̃`. -/
def transferProjector (B : Matrix V E ℝ) (w : E → ℝ) : Matrix E E ℝ :=
  (scaledInc B w)ᵀ * (shiftedWeightedLap B w)⁻¹ * scaledInc B w

def diagInvSqrt (w : E → ℝ) : Matrix E E ℝ :=
  diagonal (fun e => 1 / Real.sqrt (w e))

theorem matrix_eq_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n ℝ) (h : ∀ x, A.mulVec x = C.mulVec x) : A = C := by
  ext i j
  have hij := congr_fun (h (Pi.single j (1 : ℝ))) i
  have hA : A.mulVec (Pi.single j (1 : ℝ)) i = A i j := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have hC : C.mulVec (Pi.single j (1 : ℝ)) i = C i j := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← hA, ← hC, hij]

theorem scaledInc_gram (B : Matrix V E ℝ) (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    scaledInc B w * (scaledInc B w)ᵀ = weightedLap B w := by
  unfold scaledInc weightedLap
  rw [Matrix.transpose_mul, diagonal_transpose]
  have hsq : (diagonal fun e => Real.sqrt (w e)) * (diagonal fun e => Real.sqrt (w e)) =
      diagonal w := by
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (le_of_lt (hw i))
  rw [Matrix.mul_assoc B]
  rw [← Matrix.mul_assoc (diagonal fun e => Real.sqrt (w e))]
  rw [hsq, ← Matrix.mul_assoc]

theorem scaledInc_balanced (B : Matrix V E ℝ) (w : E → ℝ)
    (hbal : incidenceBalanced B) :
    (scaledInc B w)ᵀ.mulVec (fun _ => (1 : ℝ)) = 0 := by
  unfold scaledInc
  rw [Matrix.transpose_mul, diagonal_transpose]
  have hmul :=
    mulVec_mulVec (fun _ => (1 : ℝ)) (diagonal fun e => Real.sqrt (w e)) Bᵀ
  rw [← hmul]
  have hones : Bᵀ.mulVec (fun _ => (1 : ℝ)) = 0 := hbal
  simp [hones]

theorem scaledInc_mulVec_sum (B : Matrix V E ℝ) (w : E → ℝ) (y : E → ℝ)
    (hbal : incidenceBalanced B) :
    ∑ v, (scaledInc B w).mulVec y v = 0 := by
  have : dotProduct (fun _ => (1 : ℝ)) ((scaledInc B w).mulVec y) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
    simp [scaledInc_balanced B w hbal, dotProduct]
  simpa [dotProduct] using this

theorem inv_scaled_mean_zero (B : Matrix V E ℝ) (w : E → ℝ) (y : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w)) :
    ∑ v, ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) v = 0 := by
  set z := (shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)
  have hMz := shiftedWeightedLap_mulVec_inv B w hunit ((scaledInc B w).mulVec y)
  have hones := ones_dot_shiftedWeightedLap B w z hbal
  have : dotProduct (fun _ => (1 : ℝ)) ((shiftedWeightedLap B w).mulVec z) =
      ∑ v, (scaledInc B w).mulVec y v := by
    rw [hMz]
    simp [dotProduct]
  have : ∑ v, z v = ∑ v, (scaledInc B w).mulVec y v := hones.symm.trans this
  rw [this, scaledInc_mulVec_sum B w y hbal]

theorem meanShift_inv_scaled (B : Matrix V E ℝ) (w : E → ℝ) (y : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w)) :
    (meanShift V).mulVec
      ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) = 0 := by
  have hsum := inv_scaled_mean_zero B w y hbal hunit
  unfold meanShift
  rw [smul_mulVec, onesMatrix_mulVec]
  funext i
  change (1 / (Fintype.card V : ℝ)) • ∑ v,
      ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) v = 0
  rw [hsum]
  simp

theorem lap_inv_scaled (B : Matrix V E ℝ) (w : E → ℝ) (y : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w)) :
    (weightedLap B w).mulVec
      ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) =
      (scaledInc B w).mulVec y := by
  have hM := shiftedWeightedLap_mulVec_inv B w hunit ((scaledInc B w).mulVec y)
  have hJ := meanShift_inv_scaled B w y hbal hunit
  have hM' :
      (weightedLap B w + meanShift V).mulVec
        ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) =
        (scaledInc B w).mulVec y := by
    simpa [shiftedWeightedLap] using hM
  rw [add_mulVec, hJ, add_zero] at hM'
  exact hM'

theorem transferProjector_mulVec (B : Matrix V E ℝ) (w : E → ℝ) (y : E → ℝ) :
    (transferProjector B w).mulVec y =
      (scaledInc B w)ᵀ.mulVec
        ((shiftedWeightedLap B w)⁻¹.mulVec ((scaledInc B w).mulVec y)) := by
  simp [transferProjector, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem transferProjector_idempotent_mulVec (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (y : E → ℝ) :
    (transferProjector B w).mulVec ((transferProjector B w).mulVec y) =
      (transferProjector B w).mulVec y := by
  have hunit := shiftedWeightedLap_isUnit B w hconn hw
  set Btilde := scaledInc B w
  set z := (shiftedWeightedLap B w)⁻¹.mulVec (Btilde.mulVec y)
  have hgram : Btilde.mulVec (Btildeᵀ.mulVec z) = (weightedLap B w).mulVec z := by
    rw [mulVec_mulVec, scaledInc_gram B w hw]
  have hL := lap_inv_scaled B w y hbal hunit
  have hBy : Btilde.mulVec (Btildeᵀ.mulVec z) = Btilde.mulVec y := by
    rw [hgram, hL]
  -- Π y = B̃ᵀ z,  Π (Π y) = B̃ᵀ M⁻¹ B̃ (B̃ᵀ z) = B̃ᵀ M⁻¹ (B̃ B̃ᵀ z) = B̃ᵀ M⁻¹ (B̃ y)
  have hPiy : (transferProjector B w).mulVec y = Btildeᵀ.mulVec z :=
    transferProjector_mulVec B w y
  have hPiPi :
      (transferProjector B w).mulVec ((transferProjector B w).mulVec y) =
        Btildeᵀ.mulVec
          ((shiftedWeightedLap B w)⁻¹.mulVec (Btilde.mulVec (Btildeᵀ.mulVec z))) := by
    rw [hPiy, transferProjector_mulVec]
  rw [hPiPi, hBy]
  exact (transferProjector_mulVec B w y).symm

theorem transferProjector_idempotent (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) :
    transferProjector B w * transferProjector B w = transferProjector B w :=
  matrix_eq_of_mulVec _ _ fun y => by
    rw [← mulVec_mulVec y (transferProjector B w) (transferProjector B w)]
    exact transferProjector_idempotent_mulVec B w hbal hconn hw y

theorem transferProjector_transpose (B : Matrix V E ℝ) (w : E → ℝ) :
    (transferProjector B w)ᵀ = transferProjector B w := by
  unfold transferProjector
  have hmul :
      ((scaledInc B w)ᵀ * (shiftedWeightedLap B w)⁻¹ * scaledInc B w)ᵀ =
        (scaledInc B w)ᵀ * ((shiftedWeightedLap B w)⁻¹)ᵀ * scaledInc B w := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hmul, transpose_nonsing_inv, shiftedWeightedLap_transpose]

/-- **LAW.** `Π` is an orthogonal projector. -/
theorem transferProjector_isOrthogonalProjector (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) :
    IsOrthogonalProjector (transferProjector B w) :=
  ⟨transferProjector_transpose B w, transferProjector_idempotent B w hbal hconn hw⟩

theorem diagInvSqrt_mulVec (w : E → ℝ) (y : E → ℝ) :
    (diagInvSqrt w).mulVec y = fun e => y e / Real.sqrt (w e) := by
  funext e
  simp [diagInvSqrt, mulVec, dotProduct, diagonal, div_eq_mul_inv, mul_comm]

theorem B_eq_scaled_unscale (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) (y : E → ℝ) :
    B.mulVec y = (scaledInc B w).mulVec ((diagInvSqrt w).mulVec y) := by
  have hDI : (diagonal fun e => Real.sqrt (w e)) * diagInvSqrt w = 1 := by
    unfold diagInvSqrt
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hs : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw i))
      simp [diagonal]
      exact mul_inv_cancel₀ hs
    · simp [hij, diagonal]
  have hB : scaledInc B w * diagInvSqrt w = B := by
    unfold scaledInc
    rw [Matrix.mul_assoc, hDI, Matrix.mul_one]
  have hrew : B.mulVec y = (scaledInc B w * diagInvSqrt w).mulVec y := by
    rw [hB]
  rw [hrew]
  exact (mulVec_mulVec y (scaledInc B w) (diagInvSqrt w)).symm

theorem BT_eq_scale_proj (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) (x : V → ℝ) :
    Bᵀ.mulVec x = (diagInvSqrt w).mulVec ((scaledInc B w)ᵀ.mulVec x) := by
  -- Bᵀ = W⁻¹ᐟ² B̃ᵀ, so Bᵀ x = W⁻¹ᐟ² .* (B̃ᵀ x)
  unfold scaledInc
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, diagInvSqrt_mulVec]
  funext e
  have hs : 0 < Real.sqrt (w e) := Real.sqrt_pos.mpr (hw e)
  simp [mulVec, dotProduct, diagonal]
  field_simp [ne_of_gt hs]

/-- **LAW.** `Bᵀ M_w⁻¹ B = W⁻¹ᐟ² Π W⁻¹ᐟ²`. -/
theorem transfer_eq_cong_projector (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) (y : E → ℝ) :
    (Bᵀ * (shiftedWeightedLap B w)⁻¹ * B).mulVec y =
      (diagInvSqrt w * transferProjector B w * diagInvSqrt w).mulVec y := by
  have hy : B.mulVec y = (scaledInc B w).mulVec ((diagInvSqrt w).mulVec y) :=
    B_eq_scaled_unscale B w hw y
  have hL :
      ((shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec y)) =
        (shiftedWeightedLap B w)⁻¹.mulVec
          ((scaledInc B w).mulVec ((diagInvSqrt w).mulVec y)) := by
    rw [hy]
  have hBT := BT_eq_scale_proj B w hw
      ((shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec y))
  -- left side = Bᵀ M⁻¹ B y
  have hleft :
      (Bᵀ * (shiftedWeightedLap B w)⁻¹ * B).mulVec y =
        Bᵀ.mulVec ((shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec y)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hleft, hBT]
  -- right side
  have hright :
      (diagInvSqrt w * transferProjector B w * diagInvSqrt w).mulVec y =
        (diagInvSqrt w).mulVec
          ((transferProjector B w).mulVec ((diagInvSqrt w).mulVec y)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hright, transferProjector_mulVec, hL]

theorem transfer_eq_cong_projector_matrix (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) :
    Bᵀ * (shiftedWeightedLap B w)⁻¹ * B =
      diagInvSqrt w * transferProjector B w * diagInvSqrt w :=
  matrix_eq_of_mulVec _ _ (transfer_eq_cong_projector B w hw)

/-- **LAW (Lemma 1).** `xᵀ (Bᵀ M⁻¹ B) x ≤ xᵀ W⁻¹ x`. -/
theorem transfer_loewner_of_projector (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (x : E → ℝ) :
    dotProduct x ((Bᵀ * (shiftedWeightedLap B w)⁻¹ * B).mulVec x) ≤
      ∑ e, x e ^ 2 / w e := by
  have hP := transferProjector_isOrthogonalProjector B w hbal hconn hw
  rw [transfer_eq_cong_projector B w hw x]
  set y := (diagInvSqrt w).mulVec x
  have hy : y = fun e => x e / Real.sqrt (w e) := diagInvSqrt_mulVec w x
  have hquad :
      dotProduct x
          ((diagInvSqrt w * transferProjector B w * diagInvSqrt w).mulVec x) =
        dotProduct y ((transferProjector B w).mulVec y) := by
    have : (diagInvSqrt w * transferProjector B w * diagInvSqrt w).mulVec x =
        (diagInvSqrt w).mulVec ((transferProjector B w).mulVec y) := by
      simp [y, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [this, dotProduct_mulVec, ← mulVec_transpose]
    have hsym : (diagInvSqrt w)ᵀ = diagInvSqrt w := by
      simp [diagInvSqrt, diagonal_transpose]
    rw [hsym, dotProduct_comm]
  rw [hquad]
  have hle := projector_le_identity (transferProjector B w) hP y
  have hnorm : dotProduct y y = ∑ e, x e ^ 2 / w e := by
    rw [hy]
    simp [dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hs : 0 < Real.sqrt (w e) := Real.sqrt_pos.mpr (hw e)
    have hw0 : w e ≠ 0 := ne_of_gt (hw e)
    have hss : Real.sqrt (w e) ≠ 0 := ne_of_gt hs
    field_simp [hss, hw0]
    rw [Real.sq_sqrt (le_of_lt (hw e))]
  linarith [hle, hnorm]

end UniversalStability
