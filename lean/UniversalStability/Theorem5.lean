import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

import UniversalStability.Increment5_LeapfrogSpectrum
import UniversalStability.Increment6_ForceSmooth
import UniversalStability.Increment7_EucLyapunov
import UniversalStability.Theorem2A

/-!
# Theorem 5 — local invariance of a Lyapunov ellipsoid

Assembles the quadratic Taylor remainder of `F_c` with the kinematic
next-step bound, discharges the margin `1 − a t − b t² ≥ 1/2` for small
`t`, and iterates the Stein contraction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 400000

noncomputable section

namespace UniversalStability

open Matrix Set Metric
open scoped Matrix.Norms.L2Operator

variable {E : Type*} [Fintype E] [DecidableEq E]

def leapfrogStep (γ ΔT : ℝ) (Fc : (E → ℝ) → E → ℝ)
    (wv : (E → ℝ) × (E → ℝ)) : (E → ℝ) × (E → ℝ) :=
  (wv.1 + ΔT • wv.2, (1 - γ * ΔT) • wv.2 - ΔT • Fc (wv.1 + ΔT • wv.2))

def leapfrogOrbit (γ ΔT : ℝ) (Fc : (E → ℝ) → E → ℝ)
    (w0 v0 : E → ℝ) : ℕ → (E → ℝ) × (E → ℝ)
  | 0 => (w0, v0)
  | n + 1 => leapfrogStep γ ΔT Fc (leapfrogOrbit γ ΔT Fc w0 v0 n)

def relState (wstar : E → ℝ) (wv : (E → ℝ) × (E → ℝ)) : E ⊕ E → ℝ :=
  Sum.elim (wv.1 - wstar) wv.2

def stateW (z : E ⊕ E → ℝ) : E → ℝ := z ∘ Sum.inl

def stateV (z : E ⊕ E → ℝ) : E → ℝ := z ∘ Sum.inr

theorem sumElim_state (z : E ⊕ E → ℝ) :
    Sum.elim (stateW z) (stateV z) = z := by
  ext i
  cases i <;> rfl

theorem euc_stateW_le (z : E ⊕ E → ℝ) : euc (stateW z) ≤ euc z := by
  have hz : euc z = euc (Sum.elim (stateW z) (stateV z)) := by rw [sumElim_state]
  rw [hz, euc, euc, eucSq_sumElim]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (eucSq_nonneg _))

theorem euc_le_of_lyap_le {n : Type*} [Fintype n] {P : Matrix n n ℝ}
    {r0 : ℝ} (hr0 : 0 ≤ r0)
    (hfloor : ∀ x : n → ℝ, eucSq x ≤ lyap P x) {z : n → ℝ}
    (hz : lyap P z ≤ r0 ^ 2) : euc z ≤ r0 := by
  have : eucSq z ≤ r0 ^ 2 := (hfloor z).trans hz
  exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hr0)

theorem leapfrogLin_mulVec_elim (γ ΔT : ℝ) (H : Matrix E E ℝ)
    (δw v : E → ℝ) :
    (leapfrogLin γ ΔT H).mulVec (Sum.elim δw v) =
      Sum.elim (δw + ΔT • v)
        ((-ΔT) • H.mulVec δw +
          ((1 - γ * ΔT) • v - ΔT ^ 2 • H.mulVec v)) := by
  rw [leapfrogLin, Matrix.fromBlocks_mulVec]
  have hinl : (Sum.elim δw v ∘ Sum.inl) = δw := rfl
  have hinr : (Sum.elim δw v ∘ Sum.inr) = v := rfl
  rw [hinl, hinr]
  congr 1
  · rw [one_mulVec, smul_mulVec, one_mulVec]
  · rw [smul_mulVec, sub_mulVec, smul_mulVec, one_mulVec, smul_mulVec]

theorem mem_closedBall_of_euc [Nonempty E] {w h : E → ℝ} {ρ : ℝ}
    (hh : euc h ≤ ρ) : w + h ∈ closedBall w ρ := by
  have hdist : dist (w + h) w = ‖h‖ := by simp [dist_eq_norm]
  have hpi : ‖h‖ ≤ euc h := euc_pi_norm_le h
  simpa [mem_closedBall, hdist] using hpi.trans hh

theorem mem_positiveOrthant_of_euc_lt_coordMin [Nonempty E]
    {w h : E → ℝ} (_hw : w ∈ positiveOrthant E)
    (hh : euc h < coordMin w) : w + h ∈ positiveOrthant E := by
  intro e
  have habs : |h e| ≤ euc h := by
    simpa [Real.norm_eq_abs] using
      (le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg h)).1 le_rfl e)
        (euc_pi_norm_le h))
  have hmin : coordMin w ≤ w e := coordMin_le w e
  have hlow : w e - |h e| ≤ (w + h) e := by
    simpa [Pi.add_apply, sub_eq_add_neg] using
      add_le_add_left (neg_le_of_abs_le (le_refl |h e|)) (w e)
  have hpos : 0 < w e - |h e| :=
    sub_pos.mpr (lt_of_lt_of_le (lt_of_le_of_lt habs hh) hmin)
  exact lt_of_lt_of_le hpos hlow

theorem one_le_sqrt_one_add_sq (ΔT : ℝ) :
    (1 : ℝ) ≤ Real.sqrt (1 + ΔT ^ 2) := by
  have h1 : (1 : ℝ) ≤ 1 + ΔT ^ 2 := by nlinarith [sq_nonneg ΔT]
  simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty E]

def forceRem (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ) (wstar h : E → ℝ) :
    E → ℝ :=
  onShellForceOnShell c B eta (wstar + h) -
    onShellForceOnShell c B eta wstar -
      (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
        (onShellDrop B eta wstar)).mulVec h

def leapfrogRem (ΔT : ℝ) (RF : E → ℝ) : E ⊕ E → ℝ :=
  Sum.elim 0 (-ΔT • RF)

theorem euc_leapfrogRem (ΔT : ℝ) (RF : E → ℝ) :
    euc (leapfrogRem ΔT RF) = |ΔT| * euc RF := by
  rw [leapfrogRem, euc_sumElim_zero, euc_smul, abs_neg]

theorem forceRem_eq_taylor (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (wstar h : E → ℝ) :
    forceRem c B eta wstar h =
      onShellForceOnShell c B eta (wstar + h) -
        onShellForceOnShell c B eta wstar -
          hessianApplyCLM
            (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
              (onShellDrop B eta wstar)) h := by
  simp [forceRem, hessianApplyCLM_apply]

theorem forceRem_euc_le (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (wstar : E → ℝ) {ρ M2 : ℝ} (hMpos : 0 < M2)
    (hTaylor : ∀ h : E → ℝ, ‖h‖ ≤ ρ →
      ‖onShellForceOnShell c B eta (wstar + h) -
          onShellForceOnShell c B eta wstar -
            hessianApplyCLM
              (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
                (onShellDrop B eta wstar)) h‖ ≤
        (1 / 2) * M2 * ‖h‖ ^ 2)
    {h : E → ℝ} (hh : euc h ≤ ρ) :
    euc (forceRem c B eta wstar h) ≤
      Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * euc h ^ 2 := by
  have hpi : ‖h‖ ≤ ρ := (euc_pi_norm_le h).trans hh
  have ht := hTaylor h hpi
  have hident := forceRem_eq_taylor c B eta wstar h
  rw [hident]
  have hcard := euc_le_sqrt_card_mul_pi_norm
    (onShellForceOnShell c B eta (wstar + h) -
      onShellForceOnShell c B eta wstar -
        hessianApplyCLM
          (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
            (onShellDrop B eta wstar)) h)
  have hn : 0 ≤ Real.sqrt (Fintype.card E : ℝ) := Real.sqrt_nonneg _
  have hsq : ‖h‖ ^ 2 ≤ euc h ^ 2 :=
    (sq_le_sq₀ (norm_nonneg h) (euc_nonneg h)).mpr (euc_pi_norm_le h)
  have hM0 : 0 ≤ M2 := le_of_lt hMpos
  have ht' :
      Real.sqrt (Fintype.card E : ℝ) *
          ‖onShellForceOnShell c B eta (wstar + h) -
            onShellForceOnShell c B eta wstar -
              hessianApplyCLM
                (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
                  (onShellDrop B eta wstar)) h‖ ≤
        Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * euc h ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left ht hn
    have h2 : (1 / 2) * M2 * ‖h‖ ^ 2 ≤ (1 / 2) * M2 * euc h ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num) hM0)
    have h3 :
        Real.sqrt (Fintype.card E : ℝ) * ((1 / 2) * M2 * ‖h‖ ^ 2) ≤
          Real.sqrt (Fintype.card E : ℝ) * ((1 / 2) * M2 * euc h ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hn
    have h4 := h1.trans h3
    convert h4 using 1
    all_goals try ring
  exact hcard.trans (by convert ht' using 1)

theorem leapfrog_rel_decomp (γ ΔT : ℝ) (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) (wstar : E → ℝ)
    (hF0 : onShellForceOnShell c B eta wstar = 0)
    (w v : E → ℝ) :
    let H := onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
      (onShellDrop B eta wstar)
    let h := (w - wstar) + ΔT • v
    relState wstar (leapfrogStep γ ΔT (onShellForceOnShell c B eta) (w, v)) =
      (leapfrogLin γ ΔT H).mulVec (relState wstar (w, v)) +
        leapfrogRem ΔT (forceRem c B eta wstar h) := by
  intro H h
  have hw' : w + ΔT • v = wstar + h := by
    simp [h]
    abel
  have hFc :
      onShellForceOnShell c B eta (w + ΔT • v) =
        H.mulVec h + forceRem c B eta wstar h := by
    rw [hw']
    simp [forceRem, hF0]
    abel
  apply funext
  intro i
  cases i with
  | inl e =>
    have hlin :=
      congr_fun (leapfrogLin_mulVec_elim γ ΔT H (w - wstar) v) (Sum.inl e)
    simp [relState, leapfrogStep, leapfrogRem, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply] at hlin ⊢
    linarith
  | inr e =>
    have hlin :=
      congr_fun (leapfrogLin_mulVec_elim γ ΔT H (w - wstar) v) (Sum.inr e)
    have hHe :
        (H.mulVec h) e =
          (H.mulVec (w - wstar)) e + ΔT * (H.mulVec v) e := by
      have : H.mulVec h = H.mulVec (w - wstar) + ΔT • H.mulVec v := by
        simp [h, mulVec_add, mulVec_smul]
      simp [this, Pi.add_apply, Pi.smul_apply]
    simp [relState, leapfrogStep, leapfrogRem, hFc, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply] at hlin ⊢
    rw [hHe]
    linarith

theorem remainder_euc_le_CR (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (wstar : E → ℝ) (ΔT ρ M2 : ℝ) (hΔT : 0 < ΔT) (hMpos : 0 < M2)
    (hTaylor : ∀ h : E → ℝ, ‖h‖ ≤ ρ →
      ‖onShellForceOnShell c B eta (wstar + h) -
          onShellForceOnShell c B eta wstar -
            hessianApplyCLM
              (onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
                (onShellDrop B eta wstar)) h‖ ≤
        (1 / 2) * M2 * ‖h‖ ^ 2)
    (δw v : E → ℝ)
    (hh : euc (δw + ΔT • v) ≤ ρ) :
    euc (leapfrogRem ΔT (forceRem c B eta wstar (δw + ΔT • v))) ≤
      (ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * (1 + ΔT ^ 2)) *
        eucSq (Sum.elim δw v) := by
  set h := δw + ΔT • v
  have hRF := forceRem_euc_le c B eta wstar hMpos hTaylor hh
  have habs : |ΔT| = ΔT := abs_of_pos hΔT
  have hkin := euc_kinematic δw v ΔT
  have hkin2 : euc h ^ 2 ≤ (1 + ΔT ^ 2) * eucSq (Sum.elim δw v) := by
    have : euc h ≤ Real.sqrt (1 + ΔT ^ 2) * euc (Sum.elim δw v) := hkin
    have hnn : 0 ≤ Real.sqrt (1 + ΔT ^ 2) * euc (Sum.elim δw v) :=
      mul_nonneg (Real.sqrt_nonneg _) (euc_nonneg _)
    have := (sq_le_sq₀ (euc_nonneg h) hnn).mpr this
    rw [mul_pow, Real.sq_sqrt (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _))] at this
    have hr : euc (Sum.elim δw v) ^ 2 = eucSq (Sum.elim δw v) :=
      Real.sq_sqrt (eucSq_nonneg _)
    rwa [hr] at this
  rw [euc_leapfrogRem, habs]
  have hnnΔ : 0 ≤ ΔT := le_of_lt hΔT
  have hstep1 : ΔT * euc (forceRem c B eta wstar h) ≤
      ΔT * (Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * euc h ^ 2) :=
    mul_le_mul_of_nonneg_left hRF hnnΔ
  have hstep2 :
      ΔT * (Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * euc h ^ 2) ≤
        ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * (1 + ΔT ^ 2) *
          eucSq (Sum.elim δw v) := by
    have hfac : 0 ≤ ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 := by
      positivity
    have : euc h ^ 2 * (ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2) ≤
        ((1 + ΔT ^ 2) * eucSq (Sum.elim δw v)) *
          (ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2) :=
      mul_le_mul_of_nonneg_right hkin2 hfac
    convert this using 1
    all_goals try ring
  exact hstep1.trans (by convert hstep2 using 1)

theorem lyap_next_le (A P : Matrix (E ⊕ E) (E ⊕ E) ℝ) (z R : E ⊕ E → ℝ)
    (hlyap : Aᵀ * P * A - P = -1) (hPT : Pᵀ = P) :
    lyap P (A.mulVec z + R) ≤
      lyap P z - eucSq z +
        2 * ‖A‖ * ‖P‖ * euc z * euc R + ‖P‖ * euc R ^ 2 := by
  have hadd := lyap_add (P := P) hPT (A.mulVec z) R
  have hcontr := stein_lyap_contraction (A := A) (P := P) hlyap z
  have hcross : |A.mulVec z ⬝ᵥ P.mulVec R| ≤ euc (A.mulVec z) * euc (P.mulVec R) :=
    abs_dotProduct_le_euc _ _
  have hAz : euc (A.mulVec z) ≤ ‖A‖ * euc z := mulVec_euc_le A z
  have hPR : euc (P.mulVec R) ≤ ‖P‖ * euc R := mulVec_euc_le P R
  have h2 : 2 * (A.mulVec z ⬝ᵥ P.mulVec R) ≤
      2 * ‖A‖ * ‖P‖ * euc z * euc R := by
    have hle : A.mulVec z ⬝ᵥ P.mulVec R ≤ euc (A.mulVec z) * euc (P.mulVec R) :=
      (abs_le.mp hcross).2
    have hmul : euc (A.mulVec z) * euc (P.mulVec R) ≤
        (‖A‖ * euc z) * (‖P‖ * euc R) :=
      mul_le_mul hAz hPR (euc_nonneg _) (mul_nonneg (norm_nonneg _) (euc_nonneg _))
    have hA : 2 * (A.mulVec z ⬝ᵥ P.mulVec R) ≤
        2 * (euc (A.mulVec z) * euc (P.mulVec R)) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    have hB : 2 * (euc (A.mulVec z) * euc (P.mulVec R)) ≤
        2 * ((‖A‖ * euc z) * (‖P‖ * euc R)) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    have hC : 2 * ((‖A‖ * euc z) * (‖P‖ * euc R)) =
        2 * ‖A‖ * ‖P‖ * euc z * euc R := by ring
    exact hA.trans (hB.trans_eq hC)
  have hRsq : lyap P R ≤ ‖P‖ * euc R ^ 2 := by
    have : eucSq R = euc R ^ 2 := by
      rw [euc, Real.sq_sqrt (eucSq_nonneg R)]
    rw [← this]
    exact lyap_le_opNorm P R
  rw [hadd, hcontr]
  linarith

theorem eucSq_eq_euc_sq {n : Type*} [Fintype n] (z : n → ℝ) :
    eucSq z = euc z ^ 2 := by
  rw [euc, Real.sq_sqrt (eucSq_nonneg z)]

/-- Stein one-step bound: remainder small enough that the quadratic margin
gives the factor `1 - 1/(2 λ_M)`. -/
theorem lyap_step_contract (A P : Matrix (E ⊕ E) (E ⊕ E) ℝ) (z R : E ⊕ E → ℝ)
    (C_R : ℝ) (hlyap : Aᵀ * P * A - P = -1) (hPT : Pᵀ = P)
    (_hfloor : ∀ x, eucSq x ≤ lyap P x)
    (hR : euc R ≤ C_R * eucSq z) (hC : 0 ≤ C_R)
    (hP1 : 1 ≤ ‖P‖)
    (hmargin : (1 / 2 : ℝ) ≤
      1 - (2 * ‖A‖ * ‖P‖ * C_R) * euc z -
        (‖P‖ * C_R ^ 2) * euc z ^ 2) :
    lyap P (A.mulVec z + R) ≤ (1 - (1 / 2) / ‖P‖) * lyap P z := by
  have hP0 : 0 < ‖P‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hP1
  have hbd := lyap_next_le A P z R hlyap hPT
  have hnnR : 0 ≤ euc R := euc_nonneg _
  have h1 : 2 * ‖A‖ * ‖P‖ * euc z * euc R ≤
      2 * ‖A‖ * ‖P‖ * C_R * euc z * eucSq z := by
    have hfac : 0 ≤ 2 * ‖A‖ * ‖P‖ * euc z :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
        (norm_nonneg _)) (euc_nonneg _)
    have := mul_le_mul_of_nonneg_left hR hfac
    convert this using 1
    all_goals try ring
  have h2 : ‖P‖ * euc R ^ 2 ≤ ‖P‖ * (C_R * eucSq z) ^ 2 := by
    have hsq : euc R ^ 2 ≤ (C_R * eucSq z) ^ 2 :=
      (sq_le_sq₀ hnnR (mul_nonneg hC (eucSq_nonneg z))).mpr hR
    exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  have hexp : lyap P (A.mulVec z + R) ≤
      lyap P z - eucSq z +
        (2 * ‖A‖ * ‖P‖ * C_R) * euc z * eucSq z +
          (‖P‖ * C_R ^ 2) * eucSq z * eucSq z := by
    have : ‖P‖ * (C_R * eucSq z) ^ 2 =
        (‖P‖ * C_R ^ 2) * eucSq z * eucSq z := by ring
    linarith
  have hfactor :
      lyap P (A.mulVec z + R) ≤
        lyap P z - eucSq z *
          (1 - (2 * ‖A‖ * ‖P‖ * C_R) * euc z -
            (‖P‖ * C_R ^ 2) * euc z ^ 2) := by
    have heq : eucSq z = euc z ^ 2 := eucSq_eq_euc_sq z
    rw [heq] at hexp ⊢
    linarith
  have hhalf : lyap P (A.mulVec z + R) ≤ lyap P z - (1 / 2) * eucSq z := by
    have hnnE : 0 ≤ eucSq z := eucSq_nonneg z
    nlinarith [hfactor, hmargin, hnnE]
  have hdiv : lyap P z / ‖P‖ ≤ eucSq z :=
    (div_le_iff₀ hP0).mpr (by linarith [lyap_le_opNorm P z])
  have hrate : (1 / 2) / ‖P‖ * lyap P z ≤ (1 / 2) * eucSq z := by
    have : (1 / 2 : ℝ) / ‖P‖ * lyap P z = (1 / 2) * (lyap P z / ‖P‖) := by
      field_simp [ne_of_gt hP0]
    linarith
  have hq : (1 - (1 / 2) / ‖P‖) * lyap P z =
      lyap P z - (1 / 2) / ‖P‖ * lyap P z := by ring
  linarith [hhalf, hrate, hq]

/-- **Theorem 5.** There is a Lyapunov ellipsoid inside `Ω × ℝ^E`,
forward-invariant under the damped leapfrog map, on which the Euclidean
state decays exponentially. -/
theorem theorem5_local_invariance (c : ℝ) (hc : 0 ≤ c) (ΔT : ℝ)
    (B : Matrix V E ℝ) (eta : V → ℝ) (wstar : E → ℝ)
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ wstar e)
    (hF : ForceBalanceC c B wstar (onShellPotential B eta wstar))
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    let H := onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
      (Bᵀ.mulVec (onShellPotential B eta wstar))
    let A := leapfrogLin 3 ΔT H
    let P := steinP A
    let Fc := onShellForceOnShell c B eta
    let lamMax := ‖P‖
    ∃ r0, 0 < r0 ∧
      (∀ z : E ⊕ E → ℝ, lyap P z ≤ r0 ^ 2 →
        wstar + stateW z ∈ positiveOrthant E) ∧
      (∀ w0 v0,
        lyap P (relState wstar (w0, v0)) ≤ r0 ^ 2 →
          ∀ t : ℕ,
            (leapfrogOrbit 3 ΔT Fc w0 v0 t).1 +
                ΔT • (leapfrogOrbit 3 ΔT Fc w0 v0 t).2 ∈
              positiveOrthant E ∧
            lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
              r0 ^ 2) ∧
      (∀ w0 v0,
        lyap P (relState wstar (w0, v0)) ≤ r0 ^ 2 →
          ∀ t : ℕ,
            euc (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
              Real.sqrt lamMax *
                Real.sqrt ((1 - (1 / 2) / lamMax) ^ t) *
                  euc (relState wstar (w0, v0))) := by
  intro H A P Fc lamMax
  have hDrop : onShellDrop B eta wstar =
      Bᵀ.mulVec (onShellPotential B eta wstar) := rfl
  have hF0 : Fc wstar = 0 := by
    simpa [Fc, onShellForceOnShell, ForceBalanceC] using hF
  have hwΩ : wstar ∈ positiveOrthant E := fun e =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hadm e)
  have hρA := theorem4_spectralRadius_lt_one c hc ΔT B eta wstar
    hbal hconn hadm hF hΔT hstep
  have hstein := theorem4_stein_lyapunov c hc ΔT B eta wstar
    hbal hconn hadm hF hΔT hstep
  have hlyap : Aᵀ * P * A - P = -1 := hstein.1
  have hfloor : ∀ x, eucSq x ≤ lyap P x := fun x => by
    simpa [lyap, eucSq, dotProduct_comm] using hstein.2.2 x
  have hPT : Pᵀ = P := steinP_transpose (by simpa [A] using hρA)
  have hlam1 : (1 : ℝ) ≤ lamMax :=
    one_le_opNorm_of_quad_floor (P := P) fun x => by
      simpa [eucSq, lyap, dotProduct_comm] using hstein.2.2 x
  have hlam0 : 0 < lamMax := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hlam1
  have hmin : 0 < coordMin wstar := coordMin_pos hwΩ
  let ρ : ℝ := coordMin wstar / 2
  have hρpos : 0 < ρ := half_pos hmin
  have hρlt : ρ < coordMin wstar := half_lt_self hmin
  have hball : closedBall wstar ρ ⊆ positiveOrthant E :=
    closedBall_subset_positiveOrthant hwΩ (le_of_lt hρpos) hρlt
  obtain ⟨M2, hMpos, hTaylor⟩ :=
    onShellForceOnShell_taylor_remainder c B eta hconn wstar ρ hwΩ
      (le_of_lt hρpos) hball
  have hkin0 : 0 < Real.sqrt (1 + ΔT ^ 2) :=
    Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (by norm_num) (sq_pos_of_ne_zero (ne_of_gt hΔT)))
  let δΩ : ℝ := ρ / Real.sqrt (1 + ΔT ^ 2)
  have hδΩ : 0 < δΩ := div_pos hρpos hkin0
  let C_R : ℝ :=
    ΔT * Real.sqrt (Fintype.card E : ℝ) * (1 / 2) * M2 * (1 + ΔT ^ 2)
  have hCR0 : 0 ≤ C_R := by positivity
  let kap : ℝ := ‖A‖
  let a : ℝ := 2 * kap * lamMax * C_R
  let b : ℝ := lamMax * C_R ^ 2
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  obtain ⟨δstar, hδstar, hmargin⟩ := quadratic_margin_half ha0 hb0
  let r0 : ℝ := min δΩ δstar
  have hr0 : 0 < r0 := lt_min hδΩ hδstar
  have hr0n : 0 ≤ r0 := le_of_lt hr0
  let q : ℝ := 1 - (1 / 2) / lamMax
  have hq0 : 0 ≤ q := by
    have : (1 / 2 : ℝ) / lamMax ≤ 1 := by
      rw [div_le_one hlam0]
      linarith [hlam1]
    linarith
  have hq1 : q ≤ 1 := by
    have : 0 ≤ (1 / 2 : ℝ) / lamMax := div_nonneg (by norm_num) (le_of_lt hlam0)
    linarith
  have hδΩ_le_ρ : δΩ ≤ ρ :=
    div_le_self (le_of_lt hρpos) (one_le_sqrt_one_add_sq ΔT)
  have hellipsoid_Ω : ∀ z, lyap P z ≤ r0 ^ 2 →
      wstar + stateW z ∈ positiveOrthant E := by
    intro z hz
    have heuc : euc z ≤ r0 := euc_le_of_lyap_le hr0n hfloor hz
    have hδw : euc (stateW z) ≤ r0 := (euc_stateW_le z).trans heuc
    have : euc (stateW z) < coordMin wstar :=
      lt_of_le_of_lt (hδw.trans (min_le_left _ _))
        (lt_of_le_of_lt hδΩ_le_ρ hρlt)
    exact mem_positiveOrthant_of_euc_lt_coordMin hwΩ this
  have hnext :
      ∀ (w0 v0 : E → ℝ),
        lyap P (relState wstar (w0, v0)) ≤ r0 ^ 2 →
          (w0 + ΔT • v0 ∈ positiveOrthant E ∧
            lyap P (relState wstar (leapfrogStep 3 ΔT Fc (w0, v0))) ≤
              q * lyap P (relState wstar (w0, v0))) := by
    intro w0 v0 hz
    set z := relState wstar (w0, v0)
    set δw := w0 - wstar
    set v := v0
    set h := δw + ΔT • v
    have heuc : euc z ≤ r0 := euc_le_of_lyap_le hr0n hfloor hz
    have hzδ : z = Sum.elim δw v := rfl
    have hhkin : euc h ≤ Real.sqrt (1 + ΔT ^ 2) * euc z := by
      simpa [h, hzδ] using euc_kinematic δw v ΔT
    have hheuc : euc h ≤ ρ := by
      have hzδΩ : euc z ≤ δΩ := heuc.trans (min_le_left _ _)
      have hmul : Real.sqrt (1 + ΔT ^ 2) * euc z ≤
          Real.sqrt (1 + ΔT ^ 2) * δΩ :=
        mul_le_mul_of_nonneg_left hzδΩ (Real.sqrt_nonneg _)
      have hcancel : Real.sqrt (1 + ΔT ^ 2) * δΩ = ρ :=
        mul_div_cancel₀ ρ (ne_of_gt hkin0)
      exact hhkin.trans (hmul.trans_eq hcancel)
    have hw'Ω : w0 + ΔT • v0 ∈ positiveOrthant E := by
      have : w0 + ΔT • v0 = wstar + h := by
        simp [h, δw]
        abel
      rw [this]
      exact hball (mem_closedBall_of_euc hheuc)
    have hR := remainder_euc_le_CR c B eta wstar ΔT ρ M2 hΔT hMpos hTaylor
      δw v hheuc
    have hdecomp := leapfrog_rel_decomp 3 ΔT c B eta wstar hF0 w0 v0
    have hH : H =
        onShellHessianC c B (shiftedWeightedLap B wstar)⁻¹ wstar
          (onShellDrop B eta wstar) := by rw [hDrop]
    rw [← hH] at hdecomp
    have hz' :
        relState wstar (leapfrogStep 3 ΔT Fc (w0, v0)) =
          A.mulVec z + leapfrogRem ΔT (forceRem c B eta wstar h) := by
      simpa [A, Fc, z, h, δw, v] using hdecomp
    have hReuc : euc (leapfrogRem ΔT (forceRem c B eta wstar h)) ≤
        C_R * eucSq z := by
      simpa [C_R, h, hzδ] using hR
    have ht : euc z ≤ δstar := heuc.trans (min_le_right _ _)
    have hpar : (1 / 2 : ℝ) ≤ 1 - a * euc z - b * euc z ^ 2 :=
      hmargin (euc z) (euc_nonneg _) ht
    have hpar' : (1 / 2 : ℝ) ≤
        1 - (2 * ‖A‖ * ‖P‖ * C_R) * euc z -
          (‖P‖ * C_R ^ 2) * euc z ^ 2 := by
      simpa [a, b, kap, lamMax] using hpar
    have hcon :=
      lyap_step_contract A P z (leapfrogRem ΔT (forceRem c B eta wstar h))
        C_R hlyap hPT hfloor hReuc hCR0 hlam1 hpar'
    have hrate :
        lyap P (relState wstar (leapfrogStep 3 ΔT Fc (w0, v0))) ≤
          q * lyap P z := by
      rw [hz']
      simpa [q, lamMax] using hcon
    exact ⟨hw'Ω, by simpa [z] using hrate⟩
  have hinv : ∀ w0 v0,
      lyap P (relState wstar (w0, v0)) ≤ r0 ^ 2 →
        ∀ t : ℕ,
          (leapfrogOrbit 3 ΔT Fc w0 v0 t).1 +
              ΔT • (leapfrogOrbit 3 ΔT Fc w0 v0 t).2 ∈
            positiveOrthant E ∧
          lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
            r0 ^ 2 := by
    intro w0 v0 hz0 t
    induction t with
    | zero =>
      exact ⟨(hnext w0 v0 hz0).1, by simpa [leapfrogOrbit] using hz0⟩
    | succ t ih =>
      have hstep' := hnext (leapfrogOrbit 3 ΔT Fc w0 v0 t).1
        (leapfrogOrbit 3 ΔT Fc w0 v0 t).2 ih.2
      have horb : leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1) =
          leapfrogStep 3 ΔT Fc (leapfrogOrbit 3 ΔT Fc w0 v0 t) := rfl
      have hle :
          lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1))) ≤
            q * lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) := by
        simpa [horb] using hstep'.2
      have hVnext :
          lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1))) ≤
            r0 ^ 2 :=
        hle.trans
          ((mul_le_of_le_one_left ((eucSq_nonneg _).trans (hfloor _)) hq1).trans
            ih.2)
      have hnext' :=
        hnext (leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1)).1
          (leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1)).2 hVnext
      exact ⟨hnext'.1, hVnext⟩
  have hpow : ∀ w0 v0,
      lyap P (relState wstar (w0, v0)) ≤ r0 ^ 2 →
        ∀ t : ℕ,
          lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
            q ^ t * lyap P (relState wstar (w0, v0)) := by
    intro w0 v0 hz0 t
    induction t with
    | zero => simp [leapfrogOrbit, pow_zero, one_mul]
    | succ t ih =>
      have hst := hnext (leapfrogOrbit 3 ΔT Fc w0 v0 t).1
        (leapfrogOrbit 3 ΔT Fc w0 v0 t).2 (hinv w0 v0 hz0 t).2
      have hle :
          lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 (t + 1))) ≤
            q * lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) := by
        simpa using hst.2
      have hmul :
          q * lyap P (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
            q * (q ^ t * lyap P (relState wstar (w0, v0))) :=
        mul_le_mul_of_nonneg_left ih hq0
      have hpow' : q * (q ^ t * lyap P (relState wstar (w0, v0))) =
          q ^ (t + 1) * lyap P (relState wstar (w0, v0)) := by
        rw [pow_succ]
        ring
      exact hle.trans (hmul.trans_eq hpow')
  refine ⟨r0, hr0, hellipsoid_Ω, hinv, ?_⟩
  intro w0 v0 hz0 t
  have hV0nn : 0 ≤ lyap P (relState wstar (w0, v0)) :=
    (eucSq_nonneg _).trans (hfloor _)
  have hsqt : eucSq (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
      q ^ t * lyap P (relState wstar (w0, v0)) :=
    (hfloor _).trans (hpow w0 v0 hz0 t)
  have hnn : 0 ≤ q ^ t * lyap P (relState wstar (w0, v0)) :=
    mul_nonneg (pow_nonneg hq0 t) hV0nn
  have hsqrt :
      euc (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t)) ≤
        Real.sqrt (q ^ t) * Real.sqrt (lyap P (relState wstar (w0, v0))) := by
    calc
      euc (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t))
          = Real.sqrt (eucSq (relState wstar (leapfrogOrbit 3 ΔT Fc w0 v0 t))) :=
            rfl
      _ ≤ Real.sqrt (q ^ t * lyap P (relState wstar (w0, v0))) :=
            Real.sqrt_le_sqrt hsqt
      _ = Real.sqrt (q ^ t) * Real.sqrt (lyap P (relState wstar (w0, v0))) :=
            Real.sqrt_mul (pow_nonneg hq0 t) _
  have hVle : lyap P (relState wstar (w0, v0)) ≤
      lamMax * eucSq (relState wstar (w0, v0)) := lyap_le_opNorm P _
  have hsqrtV :
      Real.sqrt (lyap P (relState wstar (w0, v0))) ≤
        Real.sqrt lamMax * euc (relState wstar (w0, v0)) := by
    calc
      Real.sqrt (lyap P (relState wstar (w0, v0)))
          ≤ Real.sqrt (lamMax * eucSq (relState wstar (w0, v0))) :=
            Real.sqrt_le_sqrt hVle
      _ = Real.sqrt lamMax * Real.sqrt (eucSq (relState wstar (w0, v0))) :=
            Real.sqrt_mul (le_of_lt hlam0) _
      _ = Real.sqrt lamMax * euc (relState wstar (w0, v0)) := rfl
  have hprod :
      Real.sqrt (q ^ t) * Real.sqrt (lyap P (relState wstar (w0, v0))) ≤
        Real.sqrt lamMax * Real.sqrt (q ^ t) *
          euc (relState wstar (w0, v0)) := by
    have := mul_le_mul_of_nonneg_left hsqrtV (Real.sqrt_nonneg (q ^ t))
    convert this using 1
    ring
  exact hsqrt.trans (hprod.trans_eq (by ring))

end UniversalStability
