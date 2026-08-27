import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Weighted Laplacian and Thomson energy

`L_w = B diag(w) Bᵀ`. Method source: RRT `TransferLoewnerProof` (Thomson /
orthogonal remainder). No Moore–Penrose `⁺` is constructed.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Matrix Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- Weighted Laplacian `L_w = B diag(w) Bᵀ`. -/
def weightedLap (B : Matrix V E ℝ) (w : E → ℝ) : Matrix V V ℝ :=
  B * diagonal w * Bᵀ

theorem weightedLap_mulVec (B : Matrix V E ℝ) (w : E → ℝ) (Psi : V → ℝ) :
    (weightedLap B w).mulVec Psi =
      B.mulVec (fun e => w e * (Bᵀ.mulVec Psi) e) := by
  unfold weightedLap
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext e
  simp [Matrix.mulVec_diagonal]

omit [Fintype V] in
theorem weightedLap_add (B : Matrix V E ℝ) (w x : E → ℝ) :
    weightedLap B (w + x) = weightedLap B w + weightedLap B x := by
  simp only [weightedLap]
  have hd : diagonal (w + x) = diagonal w + diagonal x := (diagonal_add w x).symm
  rw [hd, Matrix.mul_add, Matrix.add_mul]

omit [Fintype V] in
theorem weightedLap_smul (B : Matrix V E ℝ) (c : ℝ) (x : E → ℝ) :
    weightedLap B (c • x) = c • weightedLap B x := by
  simp only [weightedLap]
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem weightedLap_energy (B : Matrix V E ℝ) (w : E → ℝ) (Psi : V → ℝ) :
    dotProduct Psi ((weightedLap B w).mulVec Psi) =
      ∑ e, w e * (Bᵀ.mulVec Psi e) ^ 2 := by
  rw [weightedLap_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  refine Finset.sum_congr rfl fun e _ => by
    simp
    ring

theorem weightedLap_mulVec_eq_zero_iff (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) (Psi : V → ℝ) :
    (weightedLap B w).mulVec Psi = 0 ↔ Bᵀ.mulVec Psi = 0 := by
  constructor
  · intro hL
    have hsum : ∑ e, w e * (Bᵀ.mulVec Psi e) ^ 2 = 0 := by
      have := weightedLap_energy B w Psi
      rw [hL, dotProduct_zero] at this
      exact this.symm
    have hedge : ∀ e, Bᵀ.mulVec Psi e = 0 := by
      intro e
      have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg
            (fun e _ => mul_nonneg (le_of_lt (hw e)) (sq_nonneg _))).mp
          hsum e (mem_univ e)
      have : (Bᵀ.mulVec Psi e) ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw e))
      exact eq_zero_of_pow_eq_zero this
    funext e
    exact hedge e
  · intro h
    rw [weightedLap_mulVec]
    have hz : (fun e => w e * (Bᵀ.mulVec Psi) e) = 0 := by
      funext e
      simp [congr_fun h e]
    rw [hz, mulVec_zero]

/-- Thomson: if `L_w Ψ = B y` and `w > 0`, then `yᵀ Bᵀ Ψ ≤ ∑ y_e² / w_e`. -/
theorem transfer_matrix_loewner_le_diag_inv (B : Matrix V E ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 < w e) (Psi : V → ℝ) (y : E → ℝ)
    (hsolve : (weightedLap B w).mulVec Psi = B.mulVec y) :
    dotProduct y (Bᵀ.mulVec Psi) ≤ ∑ e, y e ^ 2 / w e := by
  set dPsi := Bᵀ.mulVec Psi
  have hterm (e : E) :
      w e * (dPsi e - y e / w e) ^ 2 =
        w e * dPsi e ^ 2 - 2 * dPsi e * y e + y e ^ 2 / w e := by
    have hw0 : w e ≠ 0 := ne_of_gt (hw e)
    field_simp [hw0]
    ring
  have hnonneg : 0 ≤ ∑ e, w e * (dPsi e - y e / w e) ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (hw e)) (sq_nonneg _)
  have hsplit :
      ∑ e, w e * (dPsi e - y e / w e) ^ 2 =
        (∑ e, w e * dPsi e ^ 2) - 2 * (∑ e, dPsi e * y e) +
          ∑ e, y e ^ 2 / w e := by
    simp_rw [hterm]
    have h2 : ∑ e, 2 * dPsi e * y e = 2 * ∑ e, dPsi e * y e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => by ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  have henergy : ∑ e, w e * dPsi e ^ 2 = dotProduct y dPsi := by
    calc
      ∑ e, w e * dPsi e ^ 2
          = dotProduct Psi ((weightedLap B w).mulVec Psi) :=
            (weightedLap_energy B w Psi).symm
      _ = dotProduct Psi (B.mulVec y) := by rw [hsolve]
      _ = dotProduct (Bᵀ.mulVec Psi) y := by
            rw [dotProduct_mulVec, ← mulVec_transpose]
      _ = dotProduct y dPsi := dotProduct_comm _ _
  have hdot : ∑ e, dPsi e * y e = dotProduct y dPsi := by
    simp [dotProduct, mul_comm]
  have : 0 ≤ ∑ e, y e ^ 2 / w e - dotProduct y dPsi := by
    have := hnonneg
    rw [hsplit, henergy, hdot] at this
    linarith
  have : dotProduct y dPsi ≤ ∑ e, y e ^ 2 / w e := by linarith
  simpa [dPsi] using this

/-- `Lpinv` inverts `L_w` on every Kirchhoff load `B y`. -/
def RightInverseOnImage (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ)
    (w : E → ℝ) : Prop :=
  ∀ y : E → ℝ,
    (weightedLap B w).mulVec (Lpinv.mulVec (B.mulVec y)) = B.mulVec y

def transferApply (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ) (y : E → ℝ) :
    E → ℝ :=
  Bᵀ.mulVec (Lpinv.mulVec (B.mulVec y))

omit [DecidableEq E] in
theorem transferApply_eq_mulVec (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ)
    (y : E → ℝ) :
    transferApply B Lpinv y = (Bᵀ * Lpinv * B).mulVec y := by
  simp [transferApply, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Rayleigh form of Loewner: `yᵀ (Bᵀ L⁺ B) y ≤ yᵀ W⁻¹ y`. -/
def TransferLoewner (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ)
    (w : E → ℝ) : Prop :=
  ∀ y : E → ℝ, dotProduct y (transferApply B Lpinv y) ≤ ∑ e, y e ^ 2 / w e

theorem TransferLoewner_of_right_inverse (B : Matrix V E ℝ)
    (Lpinv : Matrix V V ℝ) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (hinv : RightInverseOnImage B Lpinv w) :
    TransferLoewner B Lpinv w := by
  intro y
  simpa [transferApply] using
    transfer_matrix_loewner_le_diag_inv B w hw
      (Lpinv.mulVec (B.mulVec y)) y (hinv y)

end UniversalStability
