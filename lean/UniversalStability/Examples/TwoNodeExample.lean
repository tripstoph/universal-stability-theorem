import Mathlib.Tactic

import UniversalStability.Theorem2B
import UniversalStability.Theorem3
import UniversalStability.Theorem5

/-!
# Two-node inhabiting instance

A path on two vertices and one edge. Theorems 1–5 are for every
`c ≥ 0`. This file inhabits them at a *coupled* point: `c = 12` and
`w★ = 1`. Kirchhoff current is `1`, so the drop is `1/w★ = 1`, and
`(c/2)(ΔΨ)² + V'(1) = 6 - 6 = 0`. Instantiating
`theorem5_local_invariance` therefore produces an `r0 > 0`, so the
hypotheses do not imply `False`.

The choice `c = 1`, `w★ = 1` is *not* an equilibrium: `V'(1) = -6` is
not cancelled by `(1/2)(ΔΨ)² = 1/2`. Coupling `c = 0` would drop the
drop-squared term entirely and is not used here.
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

/-- Coupling at which `w★ = 1` balances: `(c/2)(ΔΨ)² = 6 = -V'(1)`. -/
def twoNodeC : ℝ := 12

/-- Admissible equilibrium weight on the single edge. -/
def twoNodeWstar : Fin 1 → ℝ := fun _ => 1

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

theorem twoNodeC_nonneg : 0 ≤ twoNodeC := by
  simp [twoNodeC]

theorem twoNodeEta_sum : ∑ v : Fin 2, twoNodeEta v = 0 := by
  simp [twoNodeEta, Fin.sum_univ_two]

theorem twoNodeWstar_pos : ∀ e, (0 : ℝ) < twoNodeWstar e := by
  intro e
  simp [twoNodeWstar]

theorem twoNodeWstar_adm : ∀ e, (1 / 3 : ℝ) ≤ twoNodeWstar e := by
  intro e
  simp [twoNodeWstar]
  norm_num

theorem V'_one : V' (1 : ℝ) = -6 := by
  simp [V']

/-- Kirchhoff current is `1`, hence the on-shell drop is `1/w★ = 1`. -/
theorem twoNode_drop_eq_one :
    twoNodeBᵀ.mulVec (onShellPotential twoNodeB twoNodeEta twoNodeWstar) =
      fun _ => (1 : ℝ) := by
  set Psi := onShellPotential twoNodeB twoNodeEta twoNodeWstar
  have hunit :=
    shiftedWeightedLap_isUnit twoNodeB twoNodeWstar twoNodeB_connected
      twoNodeWstar_pos
  have hK :=
    (shiftedGreen_solves_kirchhoff twoNodeB twoNodeEta twoNodeWstar
      twoNodeB_balanced hunit twoNodeEta_sum).1
  have hI :
      twoNodeB.mulVec
          (fun e => twoNodeWstar e * (twoNodeBᵀ.mulVec Psi e)) =
        twoNodeEta := by
    simpa [weightedLap_mulVec] using hK
  have hI0 : twoNodeBᵀ.mulVec Psi 0 = 1 := by
    have h := congrFun hI 0
    simp [twoNodeB, twoNodeEta, twoNodeWstar, mulVec, dotProduct, transpose]
      at h ⊢
    exact h
  funext e
  fin_cases e
  exact hI0

theorem one_div_hundred_lt_deltaTStar : twoNodeDeltaT < deltaTStar := by
  unfold twoNodeDeltaT deltaTStar
  have h76 : (76 : ℝ) ≤ Real.sqrt 5865 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hlo : (73 : ℝ) / 1464 ≤ (-3 + Real.sqrt 5865) / 1464 := by
    have : (73 : ℝ) ≤ -3 + Real.sqrt 5865 := by linarith
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hfrac : (1 / 100 : ℝ) < 73 / 1464 := by norm_num
  exact hfrac.trans_le hlo

/-- Admissible and force-balanced at coupled `c = 12`, `w★ = 1`. -/
theorem twoNode_inhabits_hyps :
    ∃ wstar : Fin 1 → ℝ,
      (∀ e, (1 / 3 : ℝ) ≤ wstar e) ∧
      ForceBalanceC twoNodeC twoNodeB wstar
        (onShellPotential twoNodeB twoNodeEta wstar) := by
  refine ⟨twoNodeWstar, twoNodeWstar_adm, ?_⟩
  funext e
  fin_cases e
  simp [onShellForceC, twoNodeC, twoNodeWstar, twoNode_drop_eq_one, V'_one]
  norm_num

/-- Theorem 5 applies on this coupled network: hypotheses yield `r0 > 0`. -/
theorem twoNode_theorem5 :
    ∃ (wstar : Fin 1 → ℝ) (r0 : ℝ),
      (∀ e, (1 / 3 : ℝ) ≤ wstar e) ∧
      ForceBalanceC twoNodeC twoNodeB wstar
        (onShellPotential twoNodeB twoNodeEta wstar) ∧
      0 < r0 := by
  obtain ⟨wstar, hadm, hF⟩ := twoNode_inhabits_hyps
  have hth :=
    theorem5_local_invariance twoNodeC twoNodeC_nonneg
      twoNodeDeltaT twoNodeB twoNodeEta wstar twoNodeB_balanced
      twoNodeB_connected hadm hF
      (by unfold twoNodeDeltaT; norm_num) one_div_hundred_lt_deltaTStar
  obtain ⟨r0, hr0, _, _, _⟩ := hth
  exact ⟨wstar, r0, hadm, hF, hr0⟩

end UniversalStability
