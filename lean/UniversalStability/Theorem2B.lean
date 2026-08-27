import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

import UniversalStability.Constitutive
import UniversalStability.Force
import UniversalStability.ShiftedGreen
import UniversalStability.Theorem1
import UniversalStability.Theorem2A

/-!
# Theorem 2B — uniqueness by constitutive I–V monotonicity

The floor `h(w) > 0` makes the on-shell current–drop map
`σ(t) = w(t) · t` strictly increasing. Two force-balanced Kirchhoff
states therefore share drops, hence share conductances. No mountain
pass is used.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Set Matrix Finset Filter

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem V'_strictMonoOn_Ioi : StrictMonoOn V' (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hab : x < y := hxy
  have hfc : ContinuousOn V' (Icc x y) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hx hz.1
    exact (V'_hasDerivAt (ne_of_gt hz0)).continuousAt.continuousWithinAt
  have hff' : ∀ z ∈ Ioo x y, HasDerivAt V' (V'' z) z := by
    intro z hz
    exact V'_hasDerivAt (ne_of_gt (lt_trans hx hz.1))
  obtain ⟨z, hz, hMVT⟩ := exists_hasDerivAt_eq_slope (f := V') (f' := V'') hab hfc hff'
  have hden : 0 < y - x := sub_pos.mpr hab
  have hV'' : 0 < V'' z := V''_pos (lt_trans hx hz.1)
  have : 0 < (V' y - V' x) / (y - x) := by
    rwa [← hMVT]
  exact sub_pos.mp ((div_pos_iff_of_pos_right hden).mp this)

theorem exists_V'_eq (k : ℝ) : ∃ w : ℝ, 0 < w ∧ V' w = k := by
  let a : ℝ := (6 / (|k| + 7)) ^ (1 / 3 : ℝ)
  have hden : 0 < |k| + 7 := by positivity
  have ha0 : 0 < a :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hden) _
  have ha1 : a ≤ 1 := by
    have hfrac : 6 / (|k| + 7) ≤ 1 := by
      rw [div_le_one hden]
      linarith [abs_nonneg k]
    have : a ≤ (1 : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (div_nonneg (by norm_num) (le_of_lt hden)) hfrac (by norm_num)
    have : (1 : ℝ) ^ (1 / 3 : ℝ) = 1 := by
      rw [Real.one_rpow]
    linarith
  have hpow : a ^ (3 : ℕ) = 6 / (|k| + 7) := by
    have hnn : 0 ≤ 6 / (|k| + 7) := div_nonneg (by norm_num) (le_of_lt hden)
    rw [← Real.rpow_natCast, show a = (6 / (|k| + 7)) ^ (1 / 3 : ℝ) from rfl,
      ← Real.rpow_mul hnn]
    norm_num
  have hVa : V' a < k := by
    have hle := V'_le_neg_six_div_cube ha0 ha1
    have hcube : -6 / a ^ 3 = -(|k| + 7) := by
      rw [hpow]
      field_simp [ne_of_gt hden]
    have : -(|k| + 7) < k := by
      linarith [neg_le_abs k]
    linarith
  let b : ℝ := |k| + 3
  have hb1 : (1 : ℝ) ≤ b := by linarith [abs_nonneg k]
  have hVb : k < V' b := by
    have hge := V'_ge_linear hb1
    linarith [abs_nonneg k, le_abs_self k]
  have hab : a ≤ b := le_trans ha1 hb1
  have hfc : ContinuousOn V' (Icc a b) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
    exact (V'_hasDerivAt (ne_of_gt hz0)).continuousAt.continuousWithinAt
  have himg : k ∈ V' '' Icc a b :=
    intermediate_value_Icc hab hfc ⟨le_of_lt hVa, le_of_lt hVb⟩
  rcases himg with ⟨w, hwI, heq⟩
  exact ⟨w, lt_of_lt_of_le ha0 hwI.1, heq⟩

noncomputable def invV' (k : ℝ) : ℝ :=
  Classical.choose (exists_V'_eq k)

theorem invV'_pos (k : ℝ) : 0 < invV' k :=
  (Classical.choose_spec (exists_V'_eq k)).1

theorem V'_invV' (k : ℝ) : V' (invV' k) = k :=
  (Classical.choose_spec (exists_V'_eq k)).2

theorem invV'_unique {w k : ℝ} (hw : 0 < w) (h : V' w = k) : w = invV' k := by
  have := (V'_strictMonoOn_Ioi.eq_iff_eq hw (invV'_pos k)).mp
  exact this (h.trans (V'_invV' k).symm)

theorem invV'_continuousAt (k : ℝ) : ContinuousAt invV' k := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set w := invV' k
  have hw : 0 < w := invV'_pos k
  let ε' : ℝ := min ε (w / 2)
  have hε' : 0 < ε' := lt_min hε (half_pos hw)
  have hwlo : 0 < w - ε' := by
    have : ε' ≤ w / 2 := min_le_right _ _
    linarith
  have hwhi : 0 < w + ε' := add_pos hw hε'
  have hlo : V' (w - ε') < k := by
    have := V'_strictMonoOn_Ioi hwlo hw (sub_lt_self w hε')
    simpa [w, V'_invV'] using this
  have hhi : k < V' (w + ε') := by
    have := V'_strictMonoOn_Ioi hw hwhi (lt_add_of_pos_right w hε')
    simpa [w, V'_invV'] using this
  let δ : ℝ := min (k - V' (w - ε')) (V' (w + ε') - k)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  refine ⟨δ, hδ, fun k' hk' => ?_⟩
  have hklt : |k' - k| < δ := by
    simpa [Real.dist_eq] using hk'
  have hkI : V' (w - ε') < k' ∧ k' < V' (w + ε') := by
    have h1 : |k' - k| < k - V' (w - ε') :=
      lt_of_lt_of_le hklt (min_le_left _ _)
    have h2 : |k' - k| < V' (w + ε') - k :=
      lt_of_lt_of_le hklt (min_le_right _ _)
    constructor
    · have := (abs_lt.mp h1).1
      linarith
    · have := (abs_lt.mp h2).2
      linarith
  have hw' : 0 < invV' k' := invV'_pos k'
  have hlt_lo : w - ε' < invV' k' :=
    (V'_strictMonoOn_Ioi.lt_iff_lt hwlo hw').mp (by simpa [V'_invV'] using hkI.1)
  have hlt_hi : invV' k' < w + ε' :=
    (V'_strictMonoOn_Ioi.lt_iff_lt hw' hwhi).mp (by simpa [V'_invV'] using hkI.2)
  have : |invV' k' - w| < ε' := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact lt_of_lt_of_le this (min_le_left _ _)

theorem invV'_hasDerivAt (k : ℝ) :
    HasDerivAt invV' (V'' (invV' k))⁻¹ k := by
  refine HasDerivAt.of_local_left_inverse (f := V') (invV'_continuousAt k) ?_ ?_ ?_
  · exact V'_hasDerivAt (ne_of_gt (invV'_pos k))
  · exact ne_of_gt (V''_pos (invV'_pos k))
  · exact Eventually.of_forall fun y => V'_invV' y

/-- Unique positive conductance on the constitutive curve
`V'(w) = -(c/2) t²`. -/
noncomputable def eqWeight (c t : ℝ) : ℝ :=
  invV' (-c / 2 * t ^ 2)

theorem eqWeight_pos (c t : ℝ) : 0 < eqWeight c t :=
  invV'_pos _

theorem V'_eqWeight (c t : ℝ) : V' (eqWeight c t) = -c / 2 * t ^ 2 :=
  V'_invV' _

theorem eqWeight_eq_of_force {c t w : ℝ} (hw : 0 < w)
    (h : c / 2 * t ^ 2 + V' w = 0) : w = eqWeight c t :=
  invV'_unique hw (by linarith [h])

theorem eqWeight_hasDerivAt (c t : ℝ) :
    HasDerivAt (eqWeight c) ((V'' (eqWeight c t))⁻¹ * (-c * t)) t := by
  have hg : HasDerivAt (fun s : ℝ => -c / 2 * s ^ 2) (-c * t) t := by
    convert (hasDerivAt_pow 2 t).const_mul (-c / 2) using 1
    simp
    ring
  have hinv := invV'_hasDerivAt (-c / 2 * t ^ 2)
  simpa [eqWeight, smul_eq_mul] using hinv.comp t hg

/-- On-shell current as a function of drop: `σ(t) = w(t) t`. -/
noncomputable def eqCurrent (c t : ℝ) : ℝ :=
  eqWeight c t * t

theorem eqCurrent_hasDerivAt (c t : ℝ) :
    HasDerivAt (eqCurrent c)
      (eqWeight c t - c * t ^ 2 / V'' (eqWeight c t)) t := by
  have hw := eqWeight_hasDerivAt c t
  have hid := hasDerivAt_id t
  have hmul := hw.mul hid
  have hw0 : V'' (eqWeight c t) ≠ 0 := ne_of_gt (V''_pos (eqWeight_pos c t))
  convert hmul using 1
  field_simp [hw0]
  simp [id]
  ring

theorem eqCurrent_deriv_pos (c t : ℝ) :
    0 < eqWeight c t - c * t ^ 2 / V'' (eqWeight c t) := by
  set w := eqWeight c t
  have hw : 0 < w := eqWeight_pos c t
  have hV'' : 0 < V'' w := V''_pos hw
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hident : V' w = -c / 2 * t ^ 2 := V'_eqWeight c t
  have hrew : w - c * t ^ 2 / V'' w = w * h w / V'' w := by
    have hct : c * t ^ 2 = -2 * V' w := by linarith [hident]
    have hh := h_eq_V''_add_two_V'_div_w w hw0
    have h1 : w - (-2 * V' w) / V'' w = (w * V'' w + 2 * V' w) / V'' w := by
      field_simp [ne_of_gt hV'']
      ring
    have h2 : w * V'' w + 2 * V' w = w * h w := by
      rw [← hh]
      field_simp [hw0]
    rw [hct, h1, h2]
  rw [hrew]
  exact div_pos (mul_pos hw (lt_of_lt_of_le universalFloor_pos (h_ge_floor hw))) hV''

theorem eqCurrent_strictMono (c : ℝ) : StrictMono (eqCurrent c) :=
  strictMono_of_hasDerivAt_pos (eqCurrent_hasDerivAt c) (eqCurrent_deriv_pos c)

theorem eqCurrent_mul_sub_nonneg (c t s : ℝ) :
    0 ≤ (eqCurrent c t - eqCurrent c s) * (t - s) := by
  rcases le_total t s with h | h
  · have : eqCurrent c t ≤ eqCurrent c s := (eqCurrent_strictMono c).monotone h
    nlinarith
  · have : eqCurrent c s ≤ eqCurrent c t := (eqCurrent_strictMono c).monotone h
    nlinarith

theorem eqCurrent_mul_sub_eq_zero (c t s : ℝ)
    (h : (eqCurrent c t - eqCurrent c s) * (t - s) = 0) : t = s := by
  by_contra hne
  have hpos : 0 < (eqCurrent c t - eqCurrent c s) * (t - s) := by
    cases lt_or_gt_of_ne hne with
    | inl hts =>
      have : eqCurrent c t < eqCurrent c s := (eqCurrent_strictMono c) hts
      nlinarith
    | inr hst =>
      have : eqCurrent c s < eqCurrent c t := (eqCurrent_strictMono c) hst
      nlinarith
  linarith

/-- Kirchhoff currents of an on-shell force-balanced state. -/
theorem forceBalance_eqCurrent (c : ℝ) (B : Matrix V E ℝ) (w : E → ℝ)
    (Psi : V → ℝ) (hw : ∀ e, 0 < w e) (hF : ForceBalanceC c B w Psi) (e : E) :
    w e * (Bᵀ.mulVec Psi e) = eqCurrent c (Bᵀ.mulVec Psi e) := by
  have hcomp : c / 2 * (Bᵀ.mulVec Psi e) ^ 2 + V' (w e) = 0 := by
    simpa [onShellForceC] using congr_fun hF e
  have hwEq : w e = eqWeight c (Bᵀ.mulVec Psi e) :=
    eqWeight_eq_of_force (hw e) hcomp
  simp [eqCurrent, hwEq]

theorem kirchhoff_from_forceBalance (_c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) [Nonempty V] (hbal : incidenceBalanced B)
    (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e)
    (hmean : ∑ v, eta v = 0) :
    (B.mulVec fun e => w e * Bᵀ.mulVec (onShellPotential B eta w) e) = eta := by
  have hunit := shiftedWeightedLap_isUnit B w hconn hw
  have hK := (shiftedGreen_solves_kirchhoff B eta w hbal hunit hmean).1
  rwa [weightedLap_mulVec] at hK

/-- **Theorem 2B.** The on-shell equilibrium is unique. -/
theorem theorem2B_unique_on_shell_equilibrium (c : ℝ) (_hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) {w w' : E → ℝ}
    (hw : ∀ e, 0 < w e) (hw' : ∀ e, 0 < w' e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w))
    (hF' : ForceBalanceC c B w' (onShellPotential B eta w')) :
    w = w' := by
  let Ψ := onShellPotential B eta w
  let Ψ' := onShellPotential B eta w'
  let δ : E → ℝ := Bᵀ.mulVec Ψ
  let δ' : E → ℝ := Bᵀ.mulVec Ψ'
  have hI := kirchhoff_from_forceBalance c B eta w hbal hconn hw hmean
  have hI' := kirchhoff_from_forceBalance c B eta w' hbal hconn hw' hmean
  have hB : B.mulVec (fun e => w e * δ e - w' e * δ' e) = 0 := by
    have hsub :
        (fun e => w e * δ e - w' e * δ' e) =
          (fun e => w e * δ e) - fun e => w' e * δ' e := by
      funext e; rfl
    rw [hsub, mulVec_sub]
    have hIw : (B.mulVec fun e => w e * δ e) = eta := by
      simpa [δ, Ψ] using hI
    have hIw' : (B.mulVec fun e => w' e * δ' e) = eta := by
      simpa [δ', Ψ'] using hI'
    rw [hIw, hIw', sub_self]
  have hpair :
      dotProduct (fun e => w e * δ e - w' e * δ' e) (fun e => δ e - δ' e) = 0 := by
    have hδ : (fun e => δ e - δ' e) = Bᵀ.mulVec (Ψ - Ψ') := by
      funext e
      simp [δ, δ']
      rw [mulVec_sub]
      rfl
    rw [hδ, dotProduct_mulVec, ← mulVec_transpose, Matrix.transpose_transpose]
    have hIw : B.mulVec (fun e => w e * δ e - w' e * δ' e) = 0 := hB
    rw [hIw]
    simp [zero_dotProduct]
  have hterm : ∀ e, 0 ≤ (eqCurrent c (δ e) - eqCurrent c (δ' e)) * (δ e - δ' e) :=
    fun e => eqCurrent_mul_sub_nonneg c (δ e) (δ' e)
  have hσI : ∀ e, w e * δ e = eqCurrent c (δ e) :=
    fun e => forceBalance_eqCurrent c B w Ψ hw hF e
  have hσI' : ∀ e, w' e * δ' e = eqCurrent c (δ' e) :=
    fun e => forceBalance_eqCurrent c B w' Ψ' hw' hF' e
  have hsum :
      ∑ e, (eqCurrent c (δ e) - eqCurrent c (δ' e)) * (δ e - δ' e) = 0 := by
    simpa [hσI, hσI', dotProduct, sub_mul] using hpair
  have hedge : ∀ e, δ e = δ' e := by
    intro e
    have h0 := (sum_eq_zero_iff_of_nonneg fun e _ => hterm e).mp hsum e (mem_univ e)
    exact eqCurrent_mul_sub_eq_zero c (δ e) (δ' e) h0
  funext e
  have hwEq : w e = eqWeight c (δ e) := by
    have := congr_fun hF e
    simp [onShellForceC] at this
    exact eqWeight_eq_of_force (hw e) (by simpa [δ] using this)
  have hwEq' : w' e = eqWeight c (δ' e) := by
    have := congr_fun hF' e
    simp [onShellForceC] at this
    exact eqWeight_eq_of_force (hw' e) (by simpa [δ'] using this)
  rw [hwEq, hwEq', hedge e]

theorem force_zero_of_energy_fderiv (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) [Nonempty V] (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e)
    (hcrit : ∀ dw, fderiv ℝ (onShellEnergy c B eta) w dw = 0) :
    onShellForceOnShell c B eta w = 0 := by
  have hunit := shiftedWeightedLap_isUnit B w hconn hw
  have hf := onShellEnergy_hasFDerivAt_force c B eta w hunit hw
  have hpair0 : forcePairing c B eta w = 0 := by
    have hfeq : fderiv ℝ (onShellEnergy c B eta) w = forcePairing c B eta w :=
      hf.fderiv
    rw [← hfeq]
    ext dw
    exact hcrit dw
  funext e
  have hsum :
      ∑ f, onShellForceOnShell c B eta w f *
          (Pi.single e (1 : ℝ) : E → ℝ) f = 0 := by
    have := congrArg (fun L : (E → ℝ) →L[ℝ] ℝ => L (Pi.single e (1 : ℝ))) hpair0
    simpa [forcePairing] using this
  have hsingle :
      ∑ f, onShellForceOnShell c B eta w f *
          (Pi.single e (1 : ℝ) : E → ℝ) f =
        onShellForceOnShell c B eta w e := by
    rw [Finset.sum_eq_single e]
    · simp [Pi.single_eq_same]
    · intro f _ hne
      simp [Pi.single_eq_of_ne hne]
    · intro h
      exact (h (Finset.mem_univ e)).elim
  exact hsingle.symm.trans hsum

/-- **Theorem 2B (energy).** `Φ` has at most one critical point on `Ω`. -/
theorem theorem2B_unique_critical_point (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) {x y : E → ℝ}
    (hx : x ∈ positiveOrthant E) (hy : y ∈ positiveOrthant E)
    (hdx : ∀ dw, fderiv ℝ (onShellEnergy c B eta) x dw = 0)
    (hdy : ∀ dw, fderiv ℝ (onShellEnergy c B eta) y dw = 0) :
    x = y := by
  have hFx : ForceBalanceC c B x (onShellPotential B eta x) := by
    simpa [ForceBalanceC, onShellForceOnShell] using
      force_zero_of_energy_fderiv c B eta x hconn hx hdx
  have hFy : ForceBalanceC c B y (onShellPotential B eta y) := by
    simpa [ForceBalanceC, onShellForceOnShell] using
      force_zero_of_energy_fderiv c B eta y hconn hy hdy
  exact theorem2B_unique_on_shell_equilibrium c hc B eta hbal hconn hmean hx hy hFx hFy

/-- Combined with Theorem 2A: the global minimizer is the unique equilibrium. -/
theorem theorem2B_unique_minimizer (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) :
    ∃ w ∈ positiveOrthant E,
      IsMinOn (onShellEnergy c B eta) (positiveOrthant E) w ∧
        onShellForceOnShell c B eta w = 0 ∧
          ∀ w' ∈ positiveOrthant E,
            ForceBalanceC c B w' (onShellPotential B eta w') → w' = w := by
  obtain ⟨w, hw, hmin, hF⟩ :=
    exists_minimizer_on_orthant_force_zero c hc B eta hbal hconn hmean
  refine ⟨w, hw, hmin, hF, ?_⟩
  intro w' hw' hF'
  have hFw : ForceBalanceC c B w (onShellPotential B eta w) := by
    simpa [ForceBalanceC, onShellForceOnShell] using hF
  exact (theorem2B_unique_on_shell_equilibrium c hc B eta hbal hconn hmean
    hw hw' hFw hF').symm

end UniversalStability
