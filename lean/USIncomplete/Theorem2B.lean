import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

import UniversalStability.Force
import UniversalStability.Reduction
import UniversalStability.ShiftedGreen
import UniversalStability.Theorem2
import UniversalStability.Theorem2A
import UniversalStability.Theorem2B
import USIncomplete.MountainPass

/-!
# Incomplete calculus leftovers

Uniqueness of the on-shell equilibrium is now a kernel LAW
(`UniversalStability.theorem2B_unique_on_shell_equilibrium`). This file
keeps the unused mountain-pass path and the second-derivative test.
-/

set_option autoImplicit false

noncomputable section

namespace USIncomplete

open UniversalStability Set Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Second-derivative test at an on-shell critical point: Hessian floor
`18 - 9·2⁻¹/³ > 0` implies a strict local minimizer. Finite-dimensional
Taylor remainder; not yet closed. Uniqueness does not depend on this. -/
theorem crit_is_local_min_of_hessian_floor
    (c : ℝ) (hc : 0 ≤ c) (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w)) :
    IsLocalMin (onShellEnergy c B eta) w := by
  sorry

/-- Kernel uniqueness, recovered as an energy critical-point statement. -/
theorem theorem2B_unique_critical_point
    (c : ℝ) (hc : 0 ≤ c) (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) {x y : E → ℝ}
    (hx : x ∈ positiveOrthant E) (hy : y ∈ positiveOrthant E)
    (hdx : ∀ dw, fderiv ℝ (onShellEnergy c B eta) x dw = 0)
    (hdy : ∀ dw, fderiv ℝ (onShellEnergy c B eta) y dw = 0) :
    x = y :=
  UniversalStability.theorem2B_unique_critical_point c hc B eta
    hbal hconn hmean hx hy hdx hdy

end USIncomplete
