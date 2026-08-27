import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

import UniversalStability.Force
import UniversalStability.Theorem1
import UniversalStability.Theorem2A

/-!
# Increment (vi) — `ContDiff` of `F_c` and a quadratic Taylor remainder
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Finset ContinuousLinearMap Set Convex Metric
open scoped Matrix.Norms.L2Operator NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem shiftedWeightedLap_contDiff (B : Matrix V E ℝ) :
    ContDiff ℝ ⊤ (shiftedWeightedLap (V := V) (E := E) B) := by
  have hlin : ContDiff ℝ ⊤ (weightedLap (V := V) (E := E) B) :=
    (weightedLapCLM B).contDiff
  have hconst : ContDiff ℝ ⊤ fun _ : E → ℝ => meanShift V := contDiff_const
  have hfun :
      shiftedWeightedLap (V := V) (E := E) B =
        fun w => meanShift V + weightedLap B w := by
    funext w
    simp [shiftedWeightedLap, add_comm]
  rw [hfun]
  exact hconst.add hlin

theorem contDiffOn_V' : ContDiffOn ℝ ⊤ V' (Ioi (0 : ℝ)) := by
  have hid : ContDiffOn ℝ ⊤ (id : ℝ → ℝ) (Ioi (0 : ℝ)) := contDiffOn_id
  have hlin : ContDiffOn ℝ ⊤ (fun t : ℝ => (6 : ℝ) • (t - 1)) (Ioi (0 : ℝ)) :=
    ContDiffOn.const_smul (6 : ℝ) (hid.sub contDiffOn_const)
  have hpow : ContDiffOn ℝ ⊤ (fun t : ℝ => t ^ (3 : ℕ)) (Ioi (0 : ℝ)) := hid.pow 3
  have hinv : ContDiffOn ℝ ⊤ (fun t : ℝ => (t ^ (3 : ℕ))⁻¹) (Ioi (0 : ℝ)) :=
    hpow.inv fun t ht => pow_ne_zero 3 (ne_of_gt ht)
  have h6inv : ContDiffOn ℝ ⊤ (fun t : ℝ => (6 : ℝ) • (t ^ (3 : ℕ))⁻¹) (Ioi (0 : ℝ)) :=
    ContDiffOn.const_smul (6 : ℝ) hinv
  have hfun :
      V' = (fun t : ℝ => (6 : ℝ) • (t - 1)) -
        fun t : ℝ => (6 : ℝ) • (t ^ (3 : ℕ))⁻¹ := by
    funext t
    dsimp [V', Pi.sub_apply]
    rw [_root_.zpow_neg]
    rfl
  rw [hfun]
  exact hlin.sub h6inv

theorem onShellPotential_eq_ringInverse (B : Matrix V E ℝ) (eta : V → ℝ) :
    onShellPotential B eta =
      (fun M : Matrix V V ℝ => M.mulVec eta) ∘ Ring.inverse ∘
        shiftedWeightedLap B := by
  funext w
  change (shiftedWeightedLap B w)⁻¹ *ᵥ eta =
    Ring.inverse (shiftedWeightedLap B w) *ᵥ eta
  rw [nonsing_inv_eq_ringInverse]

theorem onShellPotential_contDiffOn (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) :
    ContDiffOn ℝ ⊤ (onShellPotential B eta) (positiveOrthant E) := by
  intro w hw
  have hunit := shiftedWeightedLap_isUnit B w hconn hw
  have hlap : ContDiffAt ℝ ⊤ (shiftedWeightedLap B) w :=
    (shiftedWeightedLap_contDiff B).contDiffAt
  have hinv : ContDiffAt ℝ ⊤ Ring.inverse (shiftedWeightedLap B w : Matrix V V ℝ) :=
    contDiffAt_ringInverse ℝ hunit.unit
  have hmul : ContDiff ℝ ⊤ fun M : Matrix V V ℝ => M.mulVec eta :=
    (mulVecCLM eta).contDiff
  have hcomp :=
    hmul.contDiffAt.comp w (hinv.comp w hlap)
  have hfun := onShellPotential_eq_ringInverse B eta
  rw [← hfun] at hcomp
  exact hcomp.contDiffWithinAt

theorem onShellDrop_contDiffOn (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) :
    ContDiffOn ℝ ⊤ (onShellDrop B eta) (positiveOrthant E) := by
  intro w hw
  have hΨ := (onShellPotential_contDiffOn B eta hconn w hw).contDiffAt
    (isOpen_positiveOrthant.mem_nhds hw)
  have hlin : ContDiff ℝ ⊤ fun Ψ : V → ℝ => Bᵀ.mulVec Ψ :=
    (transposeMulVecCLM B).contDiff
  have hfun : onShellDrop B eta = (fun Ψ : V → ℝ => Bᵀ.mulVec Ψ) ∘ onShellPotential B eta := by
    funext w'
    rfl
  rw [hfun]
  exact (hlin.contDiffAt.comp w hΨ).contDiffWithinAt

theorem V'_coord_contDiffOn (e : E) :
    ContDiffOn ℝ ⊤ (fun w : E → ℝ => V' (w e)) (positiveOrthant E) := by
  intro w hw
  have hcoord : ContDiff ℝ ⊤ fun w' : E → ℝ => w' e := contDiff_apply ℝ ℝ e
  have hV := (contDiffOn_V' (w e) (hw e)).contDiffAt (isOpen_Ioi.mem_nhds (hw e))
  exact (hV.comp w hcoord.contDiffAt).contDiffWithinAt

theorem dropSquare_coord_contDiffOn (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) (e : E) :
    ContDiffOn ℝ ⊤ (fun w : E → ℝ => c / 2 * (onShellDrop B eta w e) ^ 2)
      (positiveOrthant E) := by
  intro w hw
  have hdrop :=
    (onShellDrop_contDiffOn B eta hconn w hw).contDiffAt
      (isOpen_positiveOrthant.mem_nhds hw)
  have hcoord : ContDiff ℝ ⊤ fun u : E → ℝ => u e := contDiff_apply ℝ ℝ e
  have hsq : ContDiff ℝ ⊤ fun t : ℝ => c / 2 * t ^ 2 :=
    ContDiff.const_smul (c / 2) (contDiff_id.pow 2)
  have hcomp := hsq.contDiffAt.comp w (hcoord.contDiffAt.comp w hdrop)
  exact hcomp.contDiffWithinAt

/-- `F_c` is `C^∞` on the positive orthant, hence in particular `C²`. -/
theorem contDiffOn_onShellForceOnShell (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) :
    ContDiffOn ℝ ⊤ (onShellForceOnShell c B eta) (positiveOrthant E) := by
  refine contDiffOn_pi.2 fun e => ?_
  intro w hw
  have hsq := dropSquare_coord_contDiffOn c B eta hconn e w hw
  have hV := V'_coord_contDiffOn e w hw
  have hfun :
      (fun w' : E → ℝ => onShellForceOnShell c B eta w' e) =
        (fun w' => c / 2 * (onShellDrop B eta w' e) ^ 2) +
          fun w' => V' (w' e) := by
    funext w'
    simp [onShellForceOnShell, onShellForceC, onShellDrop]
  rw [hfun]
  exact (hsq.add hV)

theorem contDiffOn_Fc (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) :
    ContDiffOn ℝ 2 (onShellForceOnShell c B eta) (positiveOrthant E) :=
  (contDiffOn_onShellForceOnShell c B eta hconn).of_le (by simp)

theorem closedBall_subset_positiveOrthant [Nonempty E] {w : E → ℝ} {ρ : ℝ}
    (_hw : w ∈ positiveOrthant E) (_hρ0 : 0 ≤ ρ) (hρ : ρ < coordMin w) :
    Metric.closedBall w ρ ⊆ positiveOrthant E := by
  intro x hx e
  have hdist : dist x w ≤ ρ := Metric.mem_closedBall.mp hx
  have hn : ‖x - w‖ ≤ ρ := by
    simpa [dist_eq_norm] using hdist
  have hcoord : ‖(x - w) e‖ ≤ ρ :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg (x - w))).1 le_rfl e).trans hn
  have habs : |x e - w e| ≤ ρ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using hcoord
  have hxlow : w e - ρ ≤ x e := by
    linarith [neg_le_of_abs_le habs]
  have hmin : coordMin w ≤ w e := coordMin_le w e
  have : 0 < x e := by
    nlinarith [hmin, hρ, hxlow]
  exact this

theorem norm_mem_segment_vadd_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (w h : F) {x : F} (hx : x ∈ segment ℝ w (w + h)) : ‖x - w‖ ≤ ‖h‖ := by
  rcases hx with ⟨a, b, ha, hb, hab, rfl⟩
  have hxeq : a • w + b • (w + h) - w = b • h := by
    calc
      a • w + b • (w + h) - w
          = a • w + (b • w + b • h) - w := by rw [smul_add]
      _ = (a + b) • w + b • h - w := by rw [← add_assoc, ← add_smul]
      _ = (1 : ℝ) • w + b • h - w := by rw [hab]
      _ = w + b • h - w := by rw [one_smul]
      _ = b • h := add_sub_cancel_left _ _
  rw [hxeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have hb1 : b ≤ 1 := by linarith
  exact mul_le_of_le_one_left (norm_nonneg _) hb1

theorem pi_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    x = ∑ i : ι, Pi.single i (x i) := by
  ext j
  simp [Pi.single_apply]

theorem pi_single_eq_smul_single {ι : Type*} [DecidableEq ι] (i : ι) (c : ℝ) :
    (Pi.single i c : ι → ℝ) = c • (Pi.single i (1 : ℝ) : ι → ℝ) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [Pi.single_eq_same, smul_eq_mul]
  · simp [Pi.single_eq_of_ne h, smul_eq_mul]

theorem clm2_opNorm_le_of_partials {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] (ι → ℝ)) {M : ℝ}
    (hM : ∀ i j k, |A (Pi.single i 1) (Pi.single j 1) k| ≤ M) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) ^ 2 * max M 0 := by
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hMk : ∀ i j k, |A (Pi.single i 1) (Pi.single j 1) k| ≤ max M 0 :=
    fun i j k => (hM i j k).trans (le_max_left _ _)
  have hcoord : ∀ u v k,
      |((A u) v) k| ≤ max M 0 * (∑ i : ι, |u i|) * (∑ j : ι, |v j|) := by
    intro u v k
    have hlin :
        (A u) v =
          ∑ i, ∑ j, (u i * v j) •
            (A (Pi.single i (1 : ℝ) : ι → ℝ)
              (Pi.single j (1 : ℝ) : ι → ℝ)) := by
      have h1 : A u = ∑ i, A (Pi.single i (u i)) := by
        nth_rw 1 [pi_eq_sum_single u]
        rw [map_sum]
      rw [h1, ContinuousLinearMap.sum_apply]
      have h2 : ∀ i, A (Pi.single i (u i)) v =
          ∑ j, A (Pi.single i (u i)) (Pi.single j (v j)) := by
        intro i
        nth_rw 1 [pi_eq_sum_single v]
        rw [map_sum]
      simp_rw [h2]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [pi_single_eq_smul_single i (u i)]
      rw [ContinuousLinearMap.map_smul A]
      rw [pi_single_eq_smul_single j (v j)]
      rw [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    have hle :
        |((A u) v) k| ≤
          ∑ i, ∑ j, |u i * v j| *
            |(A (Pi.single i (1 : ℝ) : ι → ℝ)
              (Pi.single j (1 : ℝ) : ι → ℝ)) k| := by
      rw [hlin]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun i _ => (abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
    refine hle.trans ?_
    have hfac :
        ∑ i, ∑ j, |u i * v j| *
            |(A (Pi.single i (1 : ℝ) : ι → ℝ)
              (Pi.single j (1 : ℝ) : ι → ℝ)) k| ≤
          max M 0 * ∑ i, ∑ j, |u i| * |v j| := by
      have h1 :
          ∑ i, ∑ j, |u i * v j| *
              |(A (Pi.single i (1 : ℝ) : ι → ℝ)
                (Pi.single j (1 : ℝ) : ι → ℝ)) k| ≤
            ∑ i, ∑ j, |u i| * |v j| * max M 0 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hMk i j k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h2 :
          ∑ i, ∑ j, |u i| * |v j| * max M 0 =
            max M 0 * ∑ i, ∑ j, |u i| * |v j| := by
        simp [mul_comm, Finset.mul_sum, mul_assoc]
      exact h1.trans_eq h2
    have hprod :
        ∑ i, ∑ j, |u i| * |v j| = (∑ i, |u i|) * (∑ j, |v j|) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hprod] at hfac
    convert hfac using 1
    ring
  have hcard : ∀ w : ι → ℝ, ∑ i : ι, |w i| ≤ (Fintype.card ι : ℝ) * ‖w‖ := by
    intro w
    calc
      ∑ i, |w i| ≤ ∑ _i : ι, ‖w‖ :=
        Finset.sum_le_sum fun i _ => by
          simpa [Real.norm_eq_abs] using
            ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).1 le_rfl i)
      _ = (Fintype.card ι : ℝ) * ‖w‖ := by
        simp [Finset.sum_const, nsmul_eq_mul]
  refine A.opNorm_le_bound (by positivity) fun u => ?_
  refine (A u).opNorm_le_bound (by positivity) fun v => ?_
  have : ‖(A u) v‖ ≤ max M 0 * (∑ i, |u i|) * (∑ j, |v j|) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => by
      simpa [Real.norm_eq_abs] using hcoord u v k
  have : ‖(A u) v‖ ≤
      max M 0 * ((Fintype.card ι : ℝ) * ‖u‖) * ((Fintype.card ι : ℝ) * ‖v‖) := by
    refine this.trans ?_
    gcongr
    · exact hcard u
    · exact hcard v
  convert this using 1
  ring

theorem le_nested_univ_sup' {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → ι → ι → ℝ)
    (i j e : ι) :
    g i j e ≤
      Finset.univ.sup' Finset.univ_nonempty fun i' =>
        Finset.univ.sup' Finset.univ_nonempty fun j' =>
          Finset.univ.sup' Finset.univ_nonempty fun e' => g i' j' e' := by
  have h1 := Finset.le_sup' (fun e' => g i j e') (Finset.mem_univ e)
  have h2 :=
    Finset.le_sup' (fun j' => Finset.univ.sup' Finset.univ_nonempty fun e' => g i j' e')
      (Finset.mem_univ j)
  have h3 :=
    Finset.le_sup' (fun i' =>
        Finset.univ.sup' Finset.univ_nonempty fun j' =>
          Finset.univ.sup' Finset.univ_nonempty fun e' => g i' j' e')
      (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

/-- Quadratic Taylor remainder on a closed ball inside `Ω`.
`M₂` is a compact bound (twice the Lipschitz constant of `DF_c`). -/
theorem onShellForceOnShell_taylor_remainder (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) [Nonempty V] [Nonempty E] (hconn : IncidenceConnected B)
    (w : E → ℝ) (ρ : ℝ) (hw : w ∈ positiveOrthant E) (hρ0 : 0 ≤ ρ)
    (hball : Metric.closedBall w ρ ⊆ positiveOrthant E) :
    ∃ M₂ : ℝ, 0 < M₂ ∧ ∀ h : E → ℝ, ‖h‖ ≤ ρ →
      ‖onShellForceOnShell c B eta (w + h) - onShellForceOnShell c B eta w -
          hessianApplyCLM
            (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
              (onShellDrop B eta w)) h‖ ≤
        (1 / 2) * M₂ * ‖h‖ ^ 2 := by
  set f := onShellForceOnShell c B eta
  have hCtop := contDiffOn_onShellForceOnShell c B eta hconn
  have hopen := isOpen_positiveOrthant (E := E)
  have hdiff : ∀ x ∈ Metric.closedBall w ρ, DifferentiableAt ℝ f x := fun x hx =>
    ((hCtop x (hball hx)).contDiffAt (hopen.mem_nhds (hball hx))).differentiableAt (by simp)
  have hf' : ∀ x ∈ Metric.closedBall w ρ, DifferentiableAt ℝ (fderiv ℝ f) x := by
    intro x hx
    have hAt := (hCtop x (hball hx)).contDiffAt (hopen.mem_nhds (hball hx))
    exact (hAt.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hcomp : IsCompact (Metric.closedBall w ρ) := isCompact_closedBall w ρ
  have hne : (Metric.closedBall w ρ).Nonempty := ⟨w, Metric.mem_closedBall_self hρ0⟩
  let sije : E → E → E → (E → ℝ) → ℝ := fun i j e x =>
    fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) e
  have hsije : ∀ i j e, ContinuousOn (sije i j e) (Metric.closedBall w ρ) := by
    intro i j e x hx
    have hAt := (hCtop x (hball hx)).contDiffAt (hopen.mem_nhds (hball hx))
    have hA : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
      (hAt.fderiv_right (m := 1) (by simp)).continuousAt_fderiv (by simp)
    have h1 : Continuous fun A : ((E → ℝ) →L[ℝ] (E → ℝ) →L[ℝ] E → ℝ) =>
        A (Pi.single i (1 : ℝ)) := continuous_eval_const _
    have h2 : Continuous fun B : ((E → ℝ) →L[ℝ] E → ℝ) =>
        B (Pi.single j (1 : ℝ)) := continuous_eval_const _
    have h3 : Continuous fun φ : E → ℝ => φ e := continuous_apply e
    exact ((h3.comp (h2.comp h1)).continuousAt.comp hA).continuousWithinAt
  have hex : ∀ i j e, ∃ y ∈ Metric.closedBall w ρ,
      IsMaxOn (fun x => |sije i j e x|) (Metric.closedBall w ρ) y :=
    fun i j e => hcomp.exists_isMaxOn hne (hsije i j e).norm
  let yij : E → E → E → (E → ℝ) := fun i j e => Classical.choose (hex i j e)
  let M : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty fun i =>
      Finset.univ.sup' Finset.univ_nonempty fun j =>
        Finset.univ.sup' Finset.univ_nonempty fun e => |sije i j e (yij i j e)|
  have hpart : ∀ x ∈ Metric.closedBall w ρ, ∀ i j e, |sije i j e x| ≤ M := by
    intro x hx i j e
    have hy := Classical.choose_spec (hex i j e)
    have hle : |sije i j e x| ≤ |sije i j e (yij i j e)| :=
      isMaxOn_iff.1 hy.2 x hx
    exact hle.trans (le_nested_univ_sup' (fun i j e => |sije i j e (yij i j e)|) i j e)
  let L : ℝ≥0 := ⟨(Fintype.card E : ℝ) ^ 2 * max M 0, by positivity⟩
  have hbound : ∀ x ∈ Metric.closedBall w ρ, ‖fderiv ℝ (fderiv ℝ f) x‖₊ ≤ L := by
    intro x hx
    exact clm2_opNorm_le_of_partials (fderiv ℝ (fderiv ℝ f) x) (hpart x hx)
  have hlip : LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall w ρ) :=
    lipschitzOnWith_of_nnnorm_fderiv_le hf' hbound (convex_closedBall w ρ)
  refine ⟨max (2 * (L : ℝ)) 1, lt_max_iff.mpr (Or.inr (by norm_num)), fun h hh => ?_⟩
  by_cases h0 : h = 0
  · subst h0
    simp [hessianApplyCLM_apply]
  have hy : w + h ∈ Metric.closedBall w ρ := by
    have : dist (w + h) w = ‖h‖ := by simp [dist_eq_norm]
    simpa [mem_closedBall, this] using hh
  have hseg : segment ℝ w (w + h) ⊆ Metric.closedBall w ρ :=
    (convex_closedBall w ρ).segment_subset (mem_closedBall_self hρ0) hy
  have hφ :
      fderiv ℝ f w =
        hessianApplyCLM
          (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
            (onShellDrop B eta w)) :=
    (onShellForceOnShell_hasFDerivAt_of_connected c B eta w hconn hw).fderiv
  have Cbound : ∀ x ∈ segment ℝ w (w + h),
      ‖fderiv ℝ f x - fderiv ℝ f w‖ ≤ (L : ℝ) * ‖h‖ := by
    intro x hx
    have hxball : x ∈ Metric.closedBall w ρ := hseg hx
    have hlipxy := hlip.dist_le_mul x hxball w (mem_closedBall_self hρ0)
    have hxw : ‖x - w‖ ≤ ‖h‖ := norm_mem_segment_vadd_le w h hx
    calc
      ‖fderiv ℝ f x - fderiv ℝ f w‖ = dist (fderiv ℝ f x) (fderiv ℝ f w) :=
        (dist_eq_norm _ _).symm
      _ ≤ L * dist x w := hlipxy
      _ = L * ‖x - w‖ := by simp [dist_eq_norm]
      _ ≤ L * ‖h‖ := mul_le_mul_of_nonneg_left hxw L.coe_nonneg
  have hrem :=
    (convex_segment w (w + h)).norm_image_sub_le_of_norm_fderiv_le'
      (fun x hx => hdiff x (hseg hx)) Cbound
      (left_mem_segment ℝ w (w + h)) (right_mem_segment ℝ w (w + h))
  have : ‖f (w + h) - f w - fderiv ℝ f w h‖ ≤ (L : ℝ) * ‖h‖ * ‖h‖ := by
    have : (w + h) - w = h := add_sub_cancel_left w h
    simpa [this] using hrem
  rw [hφ] at this
  have hM : (L : ℝ) * ‖h‖ ^ 2 ≤ (1 / 2) * max (2 * (L : ℝ)) 1 * ‖h‖ ^ 2 := by
    have hle : (L : ℝ) ≤ (1 / 2) * max (2 * (L : ℝ)) 1 := by
      have : (2 : ℝ) * L ≤ max (2 * (L : ℝ)) 1 := le_max_left _ _
      linarith
    nlinarith [sq_nonneg ‖h‖]
  have hfin :
      ‖f (w + h) - f w -
          hessianApplyCLM
            (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
              (onShellDrop B eta w)) h‖ ≤
        (L : ℝ) * ‖h‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using this
  exact hfin.trans hM

end UniversalStability
