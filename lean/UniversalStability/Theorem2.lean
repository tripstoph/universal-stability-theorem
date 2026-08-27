import Mathlib.Tactic

import UniversalStability.Constitutive
import UniversalStability.Force
import UniversalStability.Graph
import UniversalStability.ShiftedGreen
import UniversalStability.Theorem1

/-!
# Theorem 2 — universal equilibrium Hessian floor

At force balance, `ℋ ≽ diag(h(w)) ≽ (18 - 9 · 2⁻¹/³) I` as quadratic forms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem forceBalanceC_two_scale (c : ℝ) (B : Matrix V E ℝ) (w : E → ℝ)
    (Psi : V → ℝ) (e : E) (hF : onShellForceC c B w Psi e = 0) :
    c * (Bᵀ.mulVec Psi e) ^ 2 = -2 * V' (w e) := by
  have := hF
  simp [onShellForceC] at this
  linarith

theorem h_of_forceBalance (c : ℝ) (B : Matrix V E ℝ) (w : E → ℝ)
    (Psi : V → ℝ) (e : E) (hw : w e ≠ 0)
    (hF : onShellForceC c B w Psi e = 0) :
    V'' (w e) - c * (Bᵀ.mulVec Psi e) ^ 2 / w e = h (w e) := by
  have hident := h_eq_V''_add_two_V'_div_w (w e) hw
  have hbal := forceBalanceC_two_scale c B w Psi e hF
  calc
    V'' (w e) - c * (Bᵀ.mulVec Psi e) ^ 2 / w e
        = V'' (w e) - (-2 * V' (w e)) / w e := by rw [hbal]
    _ = V'' (w e) + 2 * V' (w e) / w e := by ring
    _ = h (w e) := hident

lemma onShellHessianC_quadratic (c : ℝ) (B : Matrix V E ℝ)
    (Lpinv : Matrix V V ℝ) (w dPsi x : E → ℝ) :
    dotProduct x ((onShellHessianC c B Lpinv w dPsi).mulVec x) =
      (∑ e, V'' (w e) * x e ^ 2) -
        c * dotProduct (fun e => dPsi e * x e)
          (transferApply B Lpinv (fun e => dPsi e * x e)) := by
  have hmul := fun i => onShellHessianC_mulVec c B Lpinv w dPsi x i
  have hsplit : ∀ e,
      x e * (V'' (w e) * x e -
          c * dPsi e * transferApply B Lpinv (fun f => dPsi f * x f) e) =
        V'' (w e) * x e ^ 2 -
          c * (dPsi e * x e *
            transferApply B Lpinv (fun f => dPsi f * x f) e) := by
    intro e; ring
  have key :
      ∑ e, dPsi e * x e * transferApply B Lpinv (fun f => dPsi f * x f) e =
        dotProduct (fun e => dPsi e * x e)
          (transferApply B Lpinv (fun e => dPsi e * x e)) := by
    simp [dotProduct, mul_assoc]
  dsimp [dotProduct]
  simp_rw [hmul, hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, key]

/-- Force balance + `TransferLoewner` ⇒ `xᵀ ℋ x ≥ ∑ h(w_e) x_e²`. -/
theorem hessian_quad_ge_h (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ) (w : E → ℝ) (Psi : V → ℝ)
    (hw : ∀ e, w e ≠ 0) (hT : TransferLoewner B Lpinv w)
    (hF : ForceBalanceC c B w Psi) (x : E → ℝ) :
    dotProduct x ((onShellHessianC c B Lpinv w (Bᵀ.mulVec Psi)).mulVec x) ≥
      ∑ e, h (w e) * x e ^ 2 := by
  set dPsi := Bᵀ.mulVec Psi
  set y := fun e : E => dPsi e * x e
  have hQ := onShellHessianC_quadratic c B Lpinv w dPsi x
  have hTbound : c * dotProduct y (transferApply B Lpinv y) ≤
      c * ∑ e, y e ^ 2 / w e :=
    mul_le_mul_of_nonneg_left (hT y) hc
  have hdiag :
      ∑ e, (V'' (w e) - c * dPsi e ^ 2 / w e) * x e ^ 2 =
        ∑ e, h (w e) * x e ^ 2 := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [h_of_forceBalance c B w Psi e (hw e) (congr_fun hF e)]
  have hsplit :
      ∑ e, (V'' (w e) - c * dPsi e ^ 2 / w e) * x e ^ 2 =
        (∑ e, V'' (w e) * x e ^ 2) -
          ∑ e, (c * dPsi e ^ 2 / w e) * x e ^ 2 := by
    have hterm : ∀ e,
        (V'' (w e) - c * dPsi e ^ 2 / w e) * x e ^ 2 =
          V'' (w e) * x e ^ 2 - (c * dPsi e ^ 2 / w e) * x e ^ 2 :=
      fun e => by ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
  have hrew :
      ∑ e, (c * dPsi e ^ 2 / w e) * x e ^ 2 = c * ∑ e, y e ^ 2 / w e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    field_simp [hw e]
    ring
  calc
    dotProduct x ((onShellHessianC c B Lpinv w dPsi).mulVec x)
        = (∑ e, V'' (w e) * x e ^ 2) -
            c * dotProduct y (transferApply B Lpinv y) := hQ
    _ ≥ (∑ e, V'' (w e) * x e ^ 2) - c * ∑ e, y e ^ 2 / w e := by
        linarith [hTbound]
    _ = (∑ e, V'' (w e) * x e ^ 2) -
          ∑ e, (c * dPsi e ^ 2 / w e) * x e ^ 2 := by rw [hrew]
    _ = ∑ e, (V'' (w e) - c * dPsi e ^ 2 / w e) * x e ^ 2 := hsplit.symm
    _ = ∑ e, h (w e) * x e ^ 2 := hdiag

/-- **Theorem 2.** At equilibrium, `xᵀ ℋ x ≥ (18 - 9 · 2⁻¹/³) ‖x‖²`. -/
theorem hessian_quad_ge_floor (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (Lpinv : Matrix V V ℝ) (w : E → ℝ) (Psi : V → ℝ)
    (hw : ∀ e, 0 < w e) (hT : TransferLoewner B Lpinv w)
    (hF : ForceBalanceC c B w Psi) (x : E → ℝ) :
    dotProduct x ((onShellHessianC c B Lpinv w (Bᵀ.mulVec Psi)).mulVec x) ≥
      universalFloor * ∑ e, x e ^ 2 := by
  have hquad :=
    hessian_quad_ge_h c hc B Lpinv w Psi (fun e => ne_of_gt (hw e)) hT hF x
  have hsum :
      universalFloor * ∑ e, x e ^ 2 ≤ ∑ e, h (w e) * x e ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_right (h_ge_floor (hw e)) (sq_nonneg _)
  linarith [hquad, hsum]

/-- **Theorem 2 (shifted Green).** Connected balanced host, force balance. -/
theorem universal_equilibrium_hessian_posdef (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) [Nonempty V]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w)) (x : E → ℝ) :
    dotProduct x
        ((onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
            (Bᵀ.mulVec (onShellPotential B eta w))).mulVec x) ≥
      universalFloor * ∑ e, x e ^ 2 :=
  hessian_quad_ge_floor c hc B (shiftedWeightedLap B w)⁻¹ w
    (onShellPotential B eta w) hw
    (TransferLoewner_shifted_of_connected B w hbal hconn hw) hF x

/-- `yᵀ Bᵀ M_w⁻¹ B y ≥ 0` because `M_w` is positive definite. -/
theorem transferApply_shifted_nonneg (B : Matrix V E ℝ) (w : E → ℝ)
    (y : E → ℝ) [Nonempty V] (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) :
    0 ≤ dotProduct y (transferApply B (shiftedWeightedLap B w)⁻¹ y) := by
  have hunit := shiftedWeightedLap_isUnit B w hconn hw
  have hM := shiftedWeightedLap_posDef B w hconn hw
  set z := (shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec y)
  have hz : (shiftedWeightedLap B w).mulVec z = B.mulVec y :=
    shiftedWeightedLap_mulVec_inv B w hunit (B.mulVec y)
  have hstar : star z = z := by
    funext i; simp
  have hform : 0 ≤ z ⬝ᵥ ((shiftedWeightedLap B w).mulVec z) := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · have := hM.dotProduct_mulVec_pos hz0
      simpa [hstar] using (le_of_lt this)
  have hident :
      dotProduct y (transferApply B (shiftedWeightedLap B w)⁻¹ y) =
        z ⬝ᵥ ((shiftedWeightedLap B w).mulVec z) := by
    unfold transferApply
    have h1 : y ⬝ᵥ Bᵀ *ᵥ z = (B *ᵥ y) ⬝ᵥ z := by
      rw [dotProduct_mulVec y Bᵀ z, ← mulVec_transpose, Matrix.transpose_transpose]
    have h2 : (B *ᵥ y) ⬝ᵥ z = ((shiftedWeightedLap B w) *ᵥ z) ⬝ᵥ z := by
      rw [hz]
    exact h1.trans (h2.trans (dotProduct_comm _ _))
  rwa [hident]

/-- The interaction term is negative semidefinite, so `ℋ ≼ diag(V'')`. -/
theorem hessian_quad_le_V'' (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (Psi : V → ℝ) (w x : E → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    dotProduct x
        ((onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
            (Bᵀ.mulVec Psi)).mulVec x) ≤
      ∑ e, V'' (w e) * x e ^ 2 := by
  have hQ := onShellHessianC_quadratic c B (shiftedWeightedLap B w)⁻¹ w
    (Bᵀ.mulVec Psi) x
  have hnn := transferApply_shifted_nonneg B w
    (fun e => Bᵀ.mulVec Psi e * x e) hconn hw
  have : 0 ≤ c * dotProduct (fun e => Bᵀ.mulVec Psi e * x e)
      (transferApply B (shiftedWeightedLap B w)⁻¹
        (fun e => Bᵀ.mulVec Psi e * x e)) :=
    mul_nonneg hc hnn
  linarith [hQ]

/-- On `{w_e ≥ 1/3}`, `xᵀ ℋ x ≤ 1464 ‖x‖²`. -/
theorem hessian_quad_le_1464 (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (Psi : V → ℝ) (w x : E → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ w e) :
    dotProduct x
        ((onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
            (Bᵀ.mulVec Psi)).mulVec x) ≤
      1464 * ∑ e, x e ^ 2 := by
  have hw : ∀ e, 0 < w e := fun e =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hadm e)
  have hV := hessian_quad_le_V'' c hc B Psi w x hconn hw
  have hsum : ∑ e, V'' (w e) * x e ^ 2 ≤ 1464 * ∑ e, x e ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_right (V''_le_1464_of_adm (hadm e)) (sq_nonneg _)
  linarith

end UniversalStability
