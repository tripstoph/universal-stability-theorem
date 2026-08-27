import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

import UniversalStability.Constitutive
import UniversalStability.ShiftedGreen

/-!
# On-shell force, energy, and algebraic Hessian

`F_c(w)_e = (c/2)(ΔΨ_e)² + V'(w_e)` with `Ψ = M_w⁻¹ η` (shifted inverse).
`Φ(w) = ∑ V(w_e) - (c/2) ηᵀ M_w⁻¹ η`.
-/

set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace UniversalStability

open Matrix Finset ContinuousLinearMap

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Parametric on-shell force at a given potential. -/
def onShellForceC (c : ℝ) (B : Matrix V E ℝ) (w : E → ℝ) (Psi : V → ℝ) : E → ℝ :=
  fun e => c / 2 * (Bᵀ.mulVec Psi e) ^ 2 + V' (w e)

/-- Algebraic Hessian `ℋ = -c D_{ΔΨ} (Bᵀ L⁺ B) D_{ΔΨ} + diag(V'')`. -/
def onShellHessianC (c : ℝ) (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ)
    (w dPsi : E → ℝ) : Matrix E E ℝ :=
  fun i j =>
    (if i = j then V'' (w i) else 0) -
      c * dPsi i * (Bᵀ * Lpinv * B) i j * dPsi j

def ForceBalanceC (c : ℝ) (B : Matrix V E ℝ) (w : E → ℝ) (Psi : V → ℝ) : Prop :=
  onShellForceC c B w Psi = 0

/-- On-shell force as a map of conductances. -/
def onShellForceOnShell (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) :
    E → ℝ :=
  onShellForceC c B w (onShellPotential B eta w)

def onShellDrop (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) : E → ℝ :=
  Bᵀ.mulVec (onShellPotential B eta w)

/-- On-shell energy `Φ(w) = ∑ V - (c/2) ηᵀ M_w⁻¹ η`. -/
def onShellEnergy (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) : ℝ :=
  (∑ e, UniversalStability.V (w e)) -
    c / 2 * dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta)

omit [DecidableEq V] in
theorem shiftedWeightedLap_add (B : Matrix V E ℝ) (w h : E → ℝ) :
    shiftedWeightedLap B (w + h) = shiftedWeightedLap B w + weightedLap B h := by
  simp [shiftedWeightedLap, weightedLap_add, add_assoc, add_comm]

def weightedLapLM (B : Matrix V E ℝ) : (E → ℝ) →ₗ[ℝ] Matrix V V ℝ where
  toFun := weightedLap B
  map_add' := weightedLap_add B
  map_smul' := weightedLap_smul B

def weightedLapCLM (B : Matrix V E ℝ) : (E → ℝ) →L[ℝ] Matrix V V ℝ :=
  LinearMap.toContinuousLinearMap (weightedLapLM B)

def mulVecLM (eta : V → ℝ) : Matrix V V ℝ →ₗ[ℝ] (V → ℝ) where
  toFun := fun M => M.mulVec eta
  map_add' := by
    intro A C
    simp [add_mulVec]
  map_smul' := by
    intro r A
    simp [smul_mulVec]

def mulVecCLM (eta : V → ℝ) : Matrix V V ℝ →L[ℝ] (V → ℝ) :=
  LinearMap.toContinuousLinearMap (mulVecLM eta)

theorem shiftedWeightedLap_hasFDerivAt (B : Matrix V E ℝ) (w : E → ℝ) :
    HasFDerivAt (shiftedWeightedLap (V := V) (E := E) B) (weightedLapCLM B) w := by
  have hlin : HasFDerivAt (weightedLap (V := V) (E := E) B) (weightedLapCLM B) w :=
    (weightedLapCLM B).hasFDerivAt
  have hconst : HasFDerivAt (fun _ : E → ℝ => meanShift V)
      (0 : (E → ℝ) →L[ℝ] Matrix V V ℝ) w :=
    hasFDerivAt_const (meanShift V) w
  have hfun :
      shiftedWeightedLap (V := V) (E := E) B =
        fun w' => meanShift V + weightedLap B w' := by
    funext w'
    simp [shiftedWeightedLap, add_comm]
  rw [hfun]
  convert hconst.add hlin using 1
  exact (zero_add (weightedLapCLM B)).symm

def onShellPotentialDerivative (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) :
    (E → ℝ) →L[ℝ] (V → ℝ) :=
  let A := shiftedWeightedLap B w
  (mulVecCLM eta).comp
    ((-mulLeftRight ℝ (Matrix V V ℝ) A⁻¹ A⁻¹).comp (weightedLapCLM B))

theorem onShellPotentialDerivative_apply (B : Matrix V E ℝ) (eta : V → ℝ)
    (w dw : E → ℝ) :
    onShellPotentialDerivative B eta w dw =
      - (shiftedWeightedLap B w)⁻¹ *ᵥ
          ((weightedLap B dw).mulVec (onShellPotential B eta w)) := by
  simp [onShellPotentialDerivative, onShellPotential, mulVecCLM, mulVecLM,
    weightedLapCLM, weightedLapLM, mulLeftRight_apply, mulVec_mulVec, Matrix.mul_assoc]
  exact (neg_mulVec eta _).symm

theorem onShellPotentialDerivative_drop (B : Matrix V E ℝ) (eta : V → ℝ)
    (w dw : E → ℝ) :
    onShellPotentialDerivative B eta w dw =
      - (shiftedWeightedLap B w)⁻¹ *ᵥ
          (B.mulVec fun e =>
            dw e * (Bᵀ.mulVec (onShellPotential B eta w)) e) := by
  rw [onShellPotentialDerivative_apply, weightedLap_mulVec]

theorem onShellPotential_hasFDerivAt (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) (hunit : IsUnit (shiftedWeightedLap B w)) :
    HasFDerivAt (onShellPotential B eta) (onShellPotentialDerivative B eta w) w := by
  have hlap := shiftedWeightedLap_hasFDerivAt (V := V) (E := E) B w
  have hinv :=
    (hasFDerivAt_ringInverse (R := Matrix V V ℝ) (𝕜 := ℝ) hunit.unit).comp w hlap
  have hmul :
      HasFDerivAt (fun M : Matrix V V ℝ => M.mulVec eta) (mulVecCLM eta)
        (Ring.inverse (shiftedWeightedLap B w)) :=
    (mulVecCLM eta).hasFDerivAt
  have hcomp := hmul.comp w hinv
  have hA : (hunit.unit : Matrix V V ℝ) = shiftedWeightedLap B w := hunit.unit_spec
  have hinvA : (shiftedWeightedLap B w)⁻¹ = (↑hunit.unit⁻¹ : Matrix V V ℝ) := by
    rw [nonsing_inv_eq_ringInverse]
    have hrew : Ring.inverse (shiftedWeightedLap B w) =
        Ring.inverse (↑hunit.unit : Matrix V V ℝ) := by rw [hA]
    rw [hrew, Ring.inverse_unit]
  have hfun :
      onShellPotential B eta =
        (fun M : Matrix V V ℝ => M.mulVec eta) ∘ Ring.inverse ∘
          shiftedWeightedLap B := by
    funext w'
    change (shiftedWeightedLap B w')⁻¹ *ᵥ eta =
      Ring.inverse (shiftedWeightedLap B w') *ᵥ eta
    rw [nonsing_inv_eq_ringInverse]
  have hderiv :
      onShellPotentialDerivative B eta w =
        (mulVecCLM eta).comp
          ((-mulLeftRight ℝ (Matrix V V ℝ) (↑hunit.unit⁻¹) (↑hunit.unit⁻¹)).comp
            (weightedLapCLM B)) := by
    ext dw
    simp only [onShellPotentialDerivative, ContinuousLinearMap.comp_apply, hinvA]
  rw [hfun, hderiv]
  exact hcomp

def transposeMulVecLM (B : Matrix V E ℝ) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := fun x => Bᵀ.mulVec x
  map_add' := by
    intro x y
    simp [mulVec_add]
  map_smul' := by
    intro r x
    simp [mulVec_smul]

def transposeMulVecCLM (B : Matrix V E ℝ) : (V → ℝ) →L[ℝ] (E → ℝ) :=
  LinearMap.toContinuousLinearMap (transposeMulVecLM B)

def hessianApplyCLM (H : Matrix E E ℝ) : (E → ℝ) →L[ℝ] (E → ℝ) :=
  LinearMap.toContinuousLinearMap H.mulVecLin

omit [DecidableEq E] in
theorem hessianApplyCLM_apply (H : Matrix E E ℝ) (x : E → ℝ) :
    hessianApplyCLM H x = H.mulVec x :=
  rfl

def onShellDropDerivative (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) :
    (E → ℝ) →L[ℝ] (E → ℝ) :=
  (transposeMulVecCLM B).comp (onShellPotentialDerivative B eta w)

theorem onShellDropDerivative_apply (B : Matrix V E ℝ) (eta : V → ℝ)
    (w dw : E → ℝ) :
    onShellDropDerivative B eta w dw =
      - transferApply B (shiftedWeightedLap B w)⁻¹
          (fun e => onShellDrop B eta w e * dw e) := by
  unfold onShellDropDerivative onShellDrop transposeMulVecCLM transposeMulVecLM
    transferApply
  simp [onShellPotentialDerivative_drop]
  have hswap :
      (fun e => dw e * (Bᵀ.mulVec (onShellPotential B eta w)) e) =
        fun e => (Bᵀ.mulVec (onShellPotential B eta w)) e * dw e := by
    funext e
    ring
  rw [hswap, neg_mulVec]

end UniversalStability
