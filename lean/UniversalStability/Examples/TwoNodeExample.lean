import Mathlib.Tactic

import UniversalStability.Theorem2B
import UniversalStability.Theorem3
import UniversalStability.Theorem5

/-!
# Two-node inhabiting instance

A path on two vertices and one edge. With `c = 0`, force balance is
`V'(w★) = 0`, which has a unique positive root strictly above `1/3`.
Instantiating `theorem5_local_invariance` therefore produces an `r0 > 0`,
so the hypotheses do not imply `False`.

The numerically tempting choice `c = 1`, `w★ = 1` is *not* an
equilibrium: `V'(1) = -6` is not cancelled by `(c/2)(ΔΨ)²` at this
incidence data.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace UniversalStability

open Matrix Set

/-- Incidence `B : ℝ^{2×1}` with column `(1,-1)`. -/
def twoNodeB : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i _ => if i = 0 then (1 : ℝ) else -1

/-- Mean-zero source `(1,-1)`. -/
def twoNodeEta : Fin 2 → ℝ :=
  fun i => if i = 0 then (1 : ℝ) else -1

def twoNodeDeltaT : ℝ := 1 / 100

theorem twoNodeB_balanced : incidenceBalanced twoNodeB := by
  funext i
  simp [twoNodeB, mulVec, dotProduct, transpose]

theorem twoNodeB_connected : IncidenceConnected twoNodeB := by
  intro x hx
  have h01 : x 0 = x 1 := by
    have := congrFun hx 0
    simp [twoNodeB, mulVec, dotProduct, transpose] at this
    linarith
  refine ⟨x 0, ?_⟩
  funext i
  fin_cases i <;> simp [h01]

theorem V'_one_div_three_lt_zero : V' (1 / 3) < 0 := by
  simp [V']
  norm_num

theorem one_div_hundred_lt_deltaTStar : twoNodeDeltaT < deltaTStar := by
  unfold twoNodeDeltaT deltaTStar
  have h76 : (76 : ℝ) ≤ Real.sqrt 5865 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hlo : (73 : ℝ) / 1464 ≤ (-3 + Real.sqrt 5865) / 1464 := by
    have : (73 : ℝ) ≤ -3 + Real.sqrt 5865 := by linarith
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hfrac : (1 / 100 : ℝ) < 73 / 1464 := by norm_num
  exact hfrac.trans_le hlo

/-- Unique constitutive root of `V'` is admissible and force-balanced at `c = 0`. -/
theorem twoNode_inhabits_hyps :
    ∃ wstar : Fin 1 → ℝ,
      (∀ e, (1 / 3 : ℝ) ≤ wstar e) ∧
      ForceBalanceC 0 twoNodeB wstar
        (onShellPotential twoNodeB twoNodeEta wstar) := by
  obtain ⟨w0, hw0, hV'⟩ := exists_V'_eq (0 : ℝ)
  refine ⟨fun _ => w0, ?_, ?_⟩
  · intro e
    have hx : (1 / 3 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
    have hy : w0 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hw0
    have hf : V' (1 / 3) < V' w0 := by
      simpa [hV'] using V'_one_div_three_lt_zero
    exact le_of_lt ((V'_strictMonoOn_Ioi.lt_iff_lt hx hy).mp hf)
  · funext e
    simp [onShellForceC, hV']

/-- Theorem 5 applies on this network: hypotheses are inhabited and yield `r0 > 0`. -/
theorem twoNode_theorem5 :
    ∃ (wstar : Fin 1 → ℝ) (r0 : ℝ),
      (∀ e, (1 / 3 : ℝ) ≤ wstar e) ∧
      ForceBalanceC 0 twoNodeB wstar
        (onShellPotential twoNodeB twoNodeEta wstar) ∧
      0 < r0 := by
  obtain ⟨wstar, hadm, hF⟩ := twoNode_inhabits_hyps
  have hth :=
    theorem5_local_invariance (c := 0) (by norm_num : (0 : ℝ) ≤ 0)
      twoNodeDeltaT twoNodeB twoNodeEta wstar twoNodeB_balanced
      twoNodeB_connected hadm hF
      (by unfold twoNodeDeltaT; norm_num) one_div_hundred_lt_deltaTStar
  obtain ⟨r0, hr0, _, _, _⟩ := hth
  exact ⟨wstar, r0, hadm, hF, hr0⟩

end UniversalStability
