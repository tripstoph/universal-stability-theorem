import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

import UniversalStability.Graph

/-!
# Shifted Green map

Mathlib has no matrix Moore–Penrose `⁺`. The Green map is the shifted
inverse `(L_w + J/|V|)⁻¹`, which agrees with `L_w⁺` on mean-zero sources.

Method source: RRT `ShiftedGreen.lean` / `OnShellPotentialDeriv.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Matrix Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Each column of `B` is mean-zero: `Bᵀ 1 = 0`. -/
def incidenceBalanced (B : Matrix V E ℝ) : Prop :=
  Bᵀ.mulVec (fun _ => (1 : ℝ)) = 0

/-- `ker Bᵀ ⊆ span{1}` (connectedness of the incidence graph). -/
def IncidenceConnected (B : Matrix V E ℝ) : Prop :=
  ∀ x : V → ℝ, Bᵀ.mulVec x = 0 → ∃ c : ℝ, x = fun _ => c

def onesMatrix (V : Type*) [Fintype V] : Matrix V V ℝ :=
  fun _ _ => 1

def meanShift (V : Type*) [Fintype V] : Matrix V V ℝ :=
  (1 / (Fintype.card V : ℝ)) • onesMatrix V

def shiftedWeightedLap (B : Matrix V E ℝ) (w : E → ℝ) : Matrix V V ℝ :=
  weightedLap B w + meanShift V

def onShellPotential (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) : V → ℝ :=
  (shiftedWeightedLap B w)⁻¹ *ᵥ eta

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem onesMatrix_mulVec (x : V → ℝ) :
    (onesMatrix V).mulVec x = fun _ => ∑ v, x v := by
  funext i
  simp [onesMatrix, mulVec, dotProduct]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem onesMatrix_quadratic (x : V → ℝ) :
    dotProduct x ((onesMatrix V).mulVec x) = (∑ v, x v) ^ 2 := by
  rw [onesMatrix_mulVec]
  simp [dotProduct, ← Finset.sum_mul]
  ring

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem onesMatrix_transpose : (onesMatrix V).transpose = onesMatrix V := by
  ext i j
  rfl

omit [Fintype V] [DecidableEq V] in
theorem weightedLap_transpose (B : Matrix V E ℝ) (w : E → ℝ) :
    (weightedLap B w).transpose = weightedLap B w := by
  simp [weightedLap, Matrix.transpose_mul, diagonal_transpose, Matrix.mul_assoc]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem meanShift_transpose : (meanShift V).transpose = meanShift V := by
  simp [meanShift, onesMatrix_transpose]

omit [DecidableEq V] in
theorem shiftedWeightedLap_transpose (B : Matrix V E ℝ) (w : E → ℝ) :
    (shiftedWeightedLap B w).transpose = shiftedWeightedLap B w := by
  simp [shiftedWeightedLap, weightedLap_transpose, meanShift_transpose]

omit [DecidableEq V] in
theorem shiftedWeightedLap_isHermitian (B : Matrix V E ℝ) (w : E → ℝ) :
    (shiftedWeightedLap B w).IsHermitian := by
  change (shiftedWeightedLap B w).conjTranspose = shiftedWeightedLap B w
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, shiftedWeightedLap_transpose]

omit [DecidableEq V] in
theorem weightedLap_mulVec_ones (B : Matrix V E ℝ) (w : E → ℝ)
    (hbal : incidenceBalanced B) :
    (weightedLap B w).mulVec (fun _ => (1 : ℝ)) = 0 := by
  rw [weightedLap_mulVec]
  have hz : Bᵀ.mulVec (fun _ => (1 : ℝ)) = 0 := hbal
  simp [hz]
  exact mulVec_zero _

omit [DecidableEq V] in
theorem ones_dot_weightedLap (B : Matrix V E ℝ) (w : E → ℝ) (Psi : V → ℝ)
    (hbal : incidenceBalanced B) :
    dotProduct (fun _ => (1 : ℝ)) ((weightedLap B w).mulVec Psi) = 0 := by
  rw [weightedLap_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have hz : Bᵀ.mulVec (fun _ => (1 : ℝ)) = 0 := hbal
  simp [hz, dotProduct]

omit [DecidableEq V] in
theorem shiftedWeightedLap_quadratic (B : Matrix V E ℝ) (w : E → ℝ)
    (x : V → ℝ) :
    dotProduct x ((shiftedWeightedLap B w).mulVec x) =
      (∑ e, w e * (Bᵀ.mulVec x e) ^ 2) +
        (1 / (Fintype.card V : ℝ)) * (∑ v, x v) ^ 2 := by
  unfold shiftedWeightedLap meanShift
  rw [add_mulVec, dotProduct_add, weightedLap_energy, smul_mulVec, dotProduct_smul,
    onesMatrix_quadratic]
  simp [smul_eq_mul]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem ones_dot_meanShift (x : V → ℝ) [Nonempty V] :
    dotProduct (fun _ => (1 : ℝ)) ((meanShift V).mulVec x) = ∑ v, x v := by
  unfold meanShift
  rw [smul_mulVec, onesMatrix_mulVec]
  simp [dotProduct, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq V] in
theorem ones_dot_shiftedWeightedLap (B : Matrix V E ℝ) (w : E → ℝ) (x : V → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) :
    dotProduct (fun _ => (1 : ℝ)) ((shiftedWeightedLap B w).mulVec x) =
      ∑ v, x v := by
  unfold shiftedWeightedLap
  rw [add_mulVec, dotProduct_add, ones_dot_weightedLap B w x hbal, zero_add,
    ones_dot_meanShift]

theorem shiftedWeightedLap_mulVec_inv (B : Matrix V E ℝ) (w : E → ℝ)
    (hunit : IsUnit (shiftedWeightedLap B w)) (y : V → ℝ) :
    (shiftedWeightedLap B w).mulVec
      ((shiftedWeightedLap B w)⁻¹.mulVec y) = y := by
  haveI : Invertible (shiftedWeightedLap B w) := hunit.invertible
  rw [mulVec_mulVec y (shiftedWeightedLap B w) (shiftedWeightedLap B w)⁻¹,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

theorem onShellPotential_sum (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w)) :
    ∑ v, onShellPotential B eta w v = ∑ v, eta v := by
  have hM := shiftedWeightedLap_mulVec_inv B w hunit eta
  have hdot := ones_dot_shiftedWeightedLap B w (onShellPotential B eta w) hbal
  have hη :
      dotProduct (fun _ => (1 : ℝ))
          ((shiftedWeightedLap B w).mulVec (onShellPotential B eta w)) =
        ∑ v, eta v := by
    unfold onShellPotential
    rw [hM]
    simp [dotProduct]
  exact hdot.symm.trans hη

theorem shiftedGreen_solves_kirchhoff (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w))
    (hmean : ∑ v, eta v = 0) :
    (weightedLap B w).mulVec (onShellPotential B eta w) = eta ∧
      ∑ v, onShellPotential B eta w v = 0 := by
  have hsum := onShellPotential_sum B eta w hbal hunit
  have hΨ : ∑ v, onShellPotential B eta w v = 0 := by
    rw [hsum, hmean]
  refine ⟨?_, hΨ⟩
  have hM : (shiftedWeightedLap B w).mulVec (onShellPotential B eta w) = eta := by
    unfold onShellPotential
    exact shiftedWeightedLap_mulVec_inv B w hunit eta
  have hJ : (meanShift V).mulVec (onShellPotential B eta w) = 0 := by
    unfold meanShift
    rw [smul_mulVec, onesMatrix_mulVec]
    funext i
    simp [hΨ]
  unfold shiftedWeightedLap at hM
  rw [add_mulVec, hJ, add_zero] at hM
  exact hM

omit [DecidableEq V] in
theorem shiftedWeightedLap_posDef (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    (shiftedWeightedLap B w).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (shiftedWeightedLap_isHermitian B w) ?_
  intro x hx
  have hxstar : star x = x := by
    funext i
    simp
  rw [hxstar, shiftedWeightedLap_quadratic]
  have hn : (0 : ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr (Fintype.card_pos (α := V))
  have hdir : 0 ≤ ∑ e, w e * (Bᵀ.mulVec x e) ^ 2 :=
    Finset.sum_nonneg fun e _ =>
      mul_nonneg (le_of_lt (hw e)) (sq_nonneg _)
  have hJ : 0 ≤ (1 / (Fintype.card V : ℝ)) * (∑ v, x v) ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (le_of_lt hn)) (sq_nonneg _)
  have hform : 0 ≤
      (∑ e, w e * (Bᵀ.mulVec x e) ^ 2) +
        (1 / (Fintype.card V : ℝ)) * (∑ v, x v) ^ 2 :=
    add_nonneg hdir hJ
  refine lt_of_le_of_ne hform ?_
  intro hzero
  have hzero' :
      (∑ e, w e * (Bᵀ.mulVec x e) ^ 2) +
        (1 / (Fintype.card V : ℝ)) * (∑ v, x v) ^ 2 = 0 :=
    hzero.symm
  have hdir0 : ∑ e, w e * (Bᵀ.mulVec x e) ^ 2 = 0 := by
    linarith [hJ]
  have hJ0 : (1 / (Fintype.card V : ℝ)) * (∑ v, x v) ^ 2 = 0 := by
    linarith [hdir]
  have hedge : Bᵀ.mulVec x = 0 := by
    funext e
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg
          (fun e' _ => mul_nonneg (le_of_lt (hw e')) (sq_nonneg _))).mp
        hdir0 e (mem_univ e)
    have : (Bᵀ.mulVec x e) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw e))
    exact eq_zero_of_pow_eq_zero this
  obtain ⟨c, hc⟩ := hconn x hedge
  have hsumx : ∑ v, x v = (Fintype.card V : ℝ) * c := by
    simp [hc, Finset.card_univ, nsmul_eq_mul]
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn
  have hrew : (1 / (Fintype.card V : ℝ)) * ((Fintype.card V : ℝ) * c) ^ 2 =
      (Fintype.card V : ℝ) * c ^ 2 := by
    field_simp [hn0]
  have hnc : (Fintype.card V : ℝ) * c ^ 2 = 0 := by
    rw [hsumx] at hJ0
    rw [hrew] at hJ0
    exact hJ0
  have hc0 : c = 0 := by
    have hsq : c ^ 2 = 0 := by
      have := mul_eq_zero.mp hnc
      exact this.resolve_left hn0
    exact eq_zero_of_pow_eq_zero hsq
  apply hx
  funext v
  simp [hc, hc0]

theorem shiftedWeightedLap_isUnit (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    IsUnit (shiftedWeightedLap B w) :=
  (shiftedWeightedLap_posDef B w hconn hw).isUnit

theorem RightInverseOnImage_shifted (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B)
    (hunit : IsUnit (shiftedWeightedLap B w)) :
    RightInverseOnImage B (shiftedWeightedLap B w)⁻¹ w := by
  intro y
  have hmean : ∑ v, (B.mulVec y) v = 0 := by
    have : dotProduct (fun _ => (1 : ℝ)) (B.mulVec y) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose]
      have hz : Bᵀ.mulVec (fun _ => (1 : ℝ)) = 0 := hbal
      simp [hz, dotProduct]
    simpa [dotProduct] using this
  exact (shiftedGreen_solves_kirchhoff B (B.mulVec y) w hbal hunit hmean).1

theorem TransferLoewner_shifted_of_connected (B : Matrix V E ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) :
    TransferLoewner B (shiftedWeightedLap B w)⁻¹ w :=
  TransferLoewner_of_right_inverse B (shiftedWeightedLap B w)⁻¹ w hw
    (RightInverseOnImage_shifted B w hbal
      (shiftedWeightedLap_isUnit B w hconn hw))

end UniversalStability
