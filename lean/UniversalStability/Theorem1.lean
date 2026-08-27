import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic

import UniversalStability.Force
import UniversalStability.Graph

/-!
# Theorem 1 — Fréchet derivative of the on-shell force

The derivative of `w ↦ F_c(w)` at a unit of the **shifted** Laplacian is
matrix-vector application of `onShellHessianC`. This is not a Moore–Penrose
`HasFDerivAt`.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Matrix ContinuousLinearMap

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem on_shell_drop_hasFDerivAt (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) (hunit : IsUnit (shiftedWeightedLap B w)) :
    HasFDerivAt (onShellDrop B eta) (onShellDropDerivative B eta w) w :=
  (transposeMulVecCLM B).hasFDerivAt.comp w
    (onShellPotential_hasFDerivAt B eta w hunit)

theorem V'_hasDerivAt {t : ℝ} (ht : t ≠ 0) : HasDerivAt V' (V'' t) t := by
  have hid : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
  have hlin : HasDerivAt (fun t : ℝ => 6 * (t - 1)) 6 t := by
    convert hid.const_mul 6
    ring
  have hz := (hasDerivAt_zpow (-3) t (Or.inl ht)).const_mul (6 : ℝ)
  have hsub := hlin.sub hz
  have hfun : V' = (fun t : ℝ => 6 * (t - 1)) - fun y => 6 * y ^ (-3 : ℤ) := by
    funext x
    simp [V']
  rw [hfun]
  convert hsub using 1
  unfold V''
  have hpow : ((-3 : ℤ) - 1) = (-4 : ℤ) := rfl
  rw [hpow, Int.cast_neg, Int.cast_ofNat]
  ring

omit [DecidableEq E] in
theorem V'_coord_hasFDerivAt (w : E → ℝ) (e : E) (hw : w e ≠ 0) :
    HasFDerivAt (fun w' : E → ℝ => V' (w' e))
      (V'' (w e) • (proj (R := ℝ) (φ := fun _ : E => ℝ) e)) w := by
  have hcoord : HasFDerivAt (fun w' : E → ℝ => w' e)
      (proj (R := ℝ) (φ := fun _ : E => ℝ) e) w :=
    hasFDerivAt_apply e w
  have hbar := (V'_hasDerivAt hw).hasFDerivAt
  convert hbar.comp w hcoord using 1
  ext dw
  simp [smul_eq_mul]
  ring

omit [DecidableEq E] in
theorem dropSquare_coord_hasFDerivAt (c : ℝ) (u : E → ℝ) (e : E) :
    HasFDerivAt (fun u' : E → ℝ => c / 2 * (u' e) ^ 2)
      ((c * u e) • (proj (R := ℝ) (φ := fun _ : E => ℝ) e)) u := by
  have hcoord : HasFDerivAt (fun u' : E → ℝ => u' e)
      (proj (R := ℝ) (φ := fun _ : E => ℝ) e) u :=
    hasFDerivAt_apply e u
  have hmul := hcoord.mul hcoord
  have hsq : HasFDerivAt (fun u' : E → ℝ => (u' e) ^ 2)
      ((2 * u e) • (proj (R := ℝ) (φ := fun _ : E => ℝ) e)) u := by
    convert hmul using 1
    · ext u'
      change (u' e) ^ 2 = u' e * u' e
      exact pow_two (u' e)
    · ext dw
      simp [smul_eq_mul]
      ring
  convert hsq.const_mul (c / 2) using 1
  ext dw
  simp [smul_eq_mul]
  ring

omit [DecidableEq V] in
lemma onShellHessianC_mulVec (c : ℝ) (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ)
    (w dPsi x : E → ℝ) (i : E) :
    (onShellHessianC c B Lpinv w dPsi).mulVec x i =
      V'' (w i) * x i -
        c * dPsi i * transferApply B Lpinv (fun e => dPsi e * x e) i := by
  dsimp [onShellHessianC, Matrix.mulVec, dotProduct]
  have hterm (j : E) :
      ((if i = j then V'' (w i) else 0) -
          c * dPsi i * (Bᵀ * Lpinv * B) i j * dPsi j) * x j =
        (if i = j then V'' (w i) else 0) * x j -
          c * dPsi i * (Bᵀ * Lpinv * B) i j * dPsi j * x j := by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hdiag :
      ∑ j, (if i = j then V'' (w i) else 0) * x j = V'' (w i) * x i := by
    rw [Fintype.sum_eq_single i (fun j hne => by simp [if_neg (Ne.symm hne)])]
    simp
  have hoff :
      ∑ j, c * dPsi i * (Bᵀ * Lpinv * B) i j * dPsi j * x j =
        c * dPsi i * transferApply B Lpinv (fun e => dPsi e * x e) i := by
    rw [transferApply_eq_mulVec]
    dsimp [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag, hoff]

/-- **Theorem 1.** `HasFDerivAt` of the shifted on-shell force is `ℋ`. -/
theorem onShellForceOnShell_hasFDerivAt (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) (w : E → ℝ)
    (hunit : IsUnit (shiftedWeightedLap B w)) (hw : ∀ e, 0 < w e) :
    HasFDerivAt (onShellForceOnShell c B eta)
      (hessianApplyCLM
        (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
          (onShellDrop B eta w))) w := by
  have hdrop := on_shell_drop_hasFDerivAt B eta w hunit
  refine hasFDerivAt_pi'' fun e => ?_
  have hsq :=
    (dropSquare_coord_hasFDerivAt c (onShellDrop B eta w) e).comp w hdrop
  have hbar := V'_coord_hasFDerivAt w e (ne_of_gt (hw e))
  have hsum := hsq.add hbar
  have hfun :
      (fun w' : E → ℝ => onShellForceOnShell c B eta w' e) =
        (fun w' => c / 2 * (onShellDrop B eta w' e) ^ 2) +
          fun w' => V' (w' e) := by
    funext w'
    simp [onShellForceOnShell, onShellForceC, onShellDrop]
  rw [hfun]
  convert hsum using 1
  ext dw
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, hessianApplyCLM_apply, proj_apply]
  rw [onShellHessianC_mulVec, onShellDropDerivative_apply]
  simp [smul_eq_mul]
  ring

theorem onShellForceOnShell_hasFDerivAt_of_connected (c : ℝ)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) [Nonempty V]
    (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    HasFDerivAt (onShellForceOnShell c B eta)
      (hessianApplyCLM
        (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
          (onShellDrop B eta w))) w :=
  onShellForceOnShell_hasFDerivAt c B eta w
    (shiftedWeightedLap_isUnit B w hconn hw) hw

end UniversalStability
