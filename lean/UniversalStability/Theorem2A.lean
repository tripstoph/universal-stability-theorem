import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

import UniversalStability.Constitutive
import UniversalStability.Force
import UniversalStability.ShiftedGreen
import UniversalStability.Theorem1

/-!
# Theorem 2A — coercivity of `Φ` on `Ω = ℝ_{>0}^E`

`Φ(w) → +∞` as `w_min → 0⁺` or `w_max → +∞`. Sublevels are compact in `Ω`.
A global minimizer exists on the open orthant and is an on-shell equilibrium.
The Adm box `[1/3, 3]ᴱ` is a compact inner approximation used for Hessian
bounds, not the domain of coercivity.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Matrix Finset ContinuousLinearMap

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma electrical_nonneg (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    0 ≤ dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) := by
  have hM := shiftedWeightedLap_posDef B w hconn hw
  have hunit := hM.isUnit
  set z := (shiftedWeightedLap B w)⁻¹.mulVec eta
  have hz : (shiftedWeightedLap B w).mulVec z = eta :=
    shiftedWeightedLap_mulVec_inv B w hunit eta
  have hstar : star z = z := by
    funext i; simp
  have hform : 0 ≤ star z ⬝ᵥ ((shiftedWeightedLap B w).mulVec z) := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact le_of_lt (hM.dotProduct_mulVec_pos hz0)
  rw [hstar, hz, dotProduct_comm] at hform
  exact hform

theorem V_coercive_coords {w : ℝ} (hw : 0 < w) :
    3 / w ^ 2 ≤ UniversalStability.V w ∧ 3 * (w - 1) ^ 2 ≤ UniversalStability.V w := by
  refine ⟨V_ge_three_inv_sq hw, ?_⟩
  unfold UniversalStability.V
  have : (0 : ℝ) ≤ 3 * w ^ (-2 : ℤ) := by
    rw [_root_.zpow_neg, zpow_ofNat]
    exact div_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem onShellEnergy_le_Vsum (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) [Nonempty V]
    (hconn : IncidenceConnected B) (hw : ∀ e, 0 < w e) :
    onShellEnergy c B eta w ≤ ∑ e, UniversalStability.V (w e) := by
  unfold onShellEnergy
  have hQ := electrical_nonneg B eta w hconn hw
  have : 0 ≤ c / 2 * dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) :=
    mul_nonneg (div_nonneg hc (by norm_num)) hQ
  linarith

def admBox (E : Type*) [Fintype E] : Set (E → ℝ) :=
  {w | ∀ e, 1 / 3 ≤ w e ∧ w e ≤ 3}

theorem admBox_eq_pi {E : Type*} [Fintype E] :
    admBox E = Set.pi Set.univ (fun _ : E => Set.Icc (1 / 3 : ℝ) 3) := by
  ext w
  constructor
  · intro hw i _
    exact ⟨(hw i).1, (hw i).2⟩
  · intro hw i
    exact hw i (Set.mem_univ i)

theorem isCompact_admBox {E : Type*} [Fintype E] : IsCompact (admBox E) := by
  rw [admBox_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem admBox_nonempty {E : Type*} [Fintype E] : (admBox E).Nonempty :=
  ⟨fun _ => 1, fun _ => by constructor <;> norm_num⟩

theorem admBox_weights_pos {E : Type*} [Fintype E] {w : E → ℝ}
    (hw : w ∈ admBox E) (e : E) : 0 < w e :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hw e).1

theorem inv_transpose_shifted (B : Matrix V E ℝ) (w : E → ℝ) :
    ((shiftedWeightedLap B w)⁻¹)ᵀ = (shiftedWeightedLap B w)⁻¹ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (shiftedWeightedLap_isHermitian B w).inv.eq

/-- `η · M⁻¹ (B v) = (Bᵀ Ψ) · v`. -/
theorem eta_inv_B_dot (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) (v : E → ℝ) :
    dotProduct eta
        ((shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec v)) =
      dotProduct (Bᵀ.mulVec (onShellPotential B eta w)) v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, inv_transpose_shifted]
  simp [onShellPotential, dotProduct_mulVec, ← mulVec_transpose]

theorem electrical_fderiv_apply (B : Matrix V E ℝ) (eta : V → ℝ)
    (w dw : E → ℝ) :
    dotProduct eta (onShellPotentialDerivative B eta w dw) =
      - ∑ e, dw e * (onShellDrop B eta w e) ^ 2 := by
  let v : E → ℝ := fun e => dw e * (Bᵀ.mulVec (onShellPotential B eta w)) e
  have hdrop : onShellPotentialDerivative B eta w dw =
      -((shiftedWeightedLap B w)⁻¹.mulVec (B.mulVec v)) := by
    rw [onShellPotentialDerivative_drop, neg_mulVec]
  rw [hdrop, dotProduct_neg, eta_inv_B_dot]
  simp [v, onShellDrop, dotProduct, pow_two, mul_left_comm]

def forcePairing (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) :
    (E → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dw => ∑ e, onShellForceOnShell c B eta w e * dw e
      map_add' := fun x y => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => by ring }

theorem V_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt UniversalStability.V (V' t) t := by
  have hid : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
  have hpow : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (2 * (t - 1)) t := by
    convert hid.mul hid using 1
    · ext x; exact pow_two (x - 1)
    · ring
  have hsq : HasDerivAt (fun t : ℝ => 3 * (t - 1) ^ 2) (6 * (t - 1)) t := by
    convert hpow.const_mul 3 using 1
    ring
  have hz := (hasDerivAt_zpow (-2) t (Or.inl ht)).const_mul (3 : ℝ)
  have hadd := hsq.add hz
  have hfun : UniversalStability.V =
      (fun t : ℝ => 3 * (t - 1) ^ 2) + fun y => 3 * y ^ (-2 : ℤ) := by
    funext x
    simp [UniversalStability.V]
  rw [hfun]
  convert hadd using 1
  unfold V'
  have : ((-2 : ℤ) - 1) = (-3 : ℤ) := rfl
  rw [this, Int.cast_neg, Int.cast_ofNat]
  ring

omit [DecidableEq E] in
theorem sumV_hasFDerivAt (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    HasFDerivAt (fun w' : E → ℝ => ∑ e, UniversalStability.V (w' e))
      (∑ e, (V' (w e) • proj (R := ℝ) (φ := fun _ : E => ℝ) e)) w := by
  refine HasFDerivAt.fun_sum fun e _ => ?_
  have hcoord : HasFDerivAt (fun w' : E → ℝ => w' e)
      (proj (R := ℝ) (φ := fun _ : E => ℝ) e) w := hasFDerivAt_apply e w
  have hV := (V_hasDerivAt (ne_of_gt (hw e))).hasFDerivAt
  convert hV.comp w hcoord using 1
  ext dw
  simp [smul_eq_mul]
  ring

def pairingCLM (eta : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => dotProduct eta x
      map_add' := fun x y => by
        simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }

def electricalEnergyDerivative (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) :
    (E → ℝ) →L[ℝ] ℝ :=
  (pairingCLM eta).comp (onShellPotentialDerivative B eta w)

theorem electricalEnergy_hasFDerivAt (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) (hunit : IsUnit (shiftedWeightedLap B w)) :
    HasFDerivAt
      (fun w' : E → ℝ =>
        dotProduct eta ((shiftedWeightedLap B w')⁻¹.mulVec eta))
      (electricalEnergyDerivative B eta w) w := by
  have hΨ := onShellPotential_hasFDerivAt B eta w hunit
  have hlin :
      HasFDerivAt (fun Ψ : V → ℝ => dotProduct eta Ψ) (pairingCLM eta)
        (onShellPotential B eta w) :=
    (pairingCLM eta).hasFDerivAt
  convert hlin.comp w hΨ using 1

/-- **Lemma 2.** `HasFDerivAt Φ = pairing with F_c`. -/
theorem onShellEnergy_hasFDerivAt_force (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) (w : E → ℝ)
    (hunit : IsUnit (shiftedWeightedLap B w)) (hw : ∀ e, 0 < w e) :
    HasFDerivAt (onShellEnergy c B eta) (forcePairing c B eta w) w := by
  have hV := sumV_hasFDerivAt (E := E) w hw
  have hE := electricalEnergy_hasFDerivAt B eta w hunit
  have hE2 := hE.const_mul (c / 2)
  have hsub := hV.sub hE2
  have hfun :
      onShellEnergy c B eta =
        (fun w' => ∑ e, UniversalStability.V (w' e)) -
          fun w' => c / 2 *
            dotProduct eta ((shiftedWeightedLap B w')⁻¹.mulVec eta) := by
    funext w'
    simp [onShellEnergy]
  rw [hfun]
  convert hsub using 1
  ext dw
  have hEapp :
      pairingCLM eta (onShellPotentialDerivative B eta w dw) =
        - ∑ e, dw e * (onShellDrop B eta w e) ^ 2 :=
    electrical_fderiv_apply B eta w dw
  simp [forcePairing, onShellForceOnShell, onShellForceC, onShellDrop,
    electricalEnergyDerivative, hEapp]
  simp_rw [add_mul, sum_add_distrib]
  rw [add_comm]
  congr 1
  simp_rw [mul_assoc]
  rw [← mul_sum]
  exact congrArg (fun t => c / 2 * t)
    (sum_congr rfl fun x _ => mul_comm _ _)

/-- **LAW.** A local minimizer of `Φ` is an on-shell equilibrium. -/
theorem localMin_force_zero (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    (w : E → ℝ) (hunit : IsUnit (shiftedWeightedLap B w))
    (hw : ∀ e, 0 < w e)
    (hmin : IsLocalMin (onShellEnergy c B eta) w) :
    onShellForceOnShell c B eta w = 0 := by
  have hf := onShellEnergy_hasFDerivAt_force c B eta w hunit hw
  have hder := hmin.hasFDerivAt_eq_zero hf
  funext e
  have hpair :=
    congrArg (fun L : (E → ℝ) →L[ℝ] ℝ => L (Pi.single e (1 : ℝ))) hder
  have h0 : forcePairing c B eta w (Pi.single e (1 : ℝ)) = 0 := by
    simpa using hpair
  have hsum :
      ∑ f, onShellForceOnShell c B eta w f * (Pi.single e (1 : ℝ) : E → ℝ) f = 0 := by
    simpa [forcePairing] using h0
  have hsingle :
      ∑ f, onShellForceOnShell c B eta w f * (Pi.single e (1 : ℝ) : E → ℝ) f =
        onShellForceOnShell c B eta w e := by
    rw [Finset.sum_eq_single e]
    · simp [Pi.single_eq_same]
    · intro f _ hne
      simp [Pi.single_eq_of_ne hne]
    · intro h
      exact (h (Finset.mem_univ e)).elim
  exact hsingle.symm.trans hsum

theorem onShellEnergy_continuousOn_adm (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) [Nonempty V] (hconn : IncidenceConnected B) :
    ContinuousOn (onShellEnergy c B eta) (admBox E) := by
  intro w hw
  have hwpos : ∀ e, 0 < w e := fun e => admBox_weights_pos hw e
  have hunit := shiftedWeightedLap_isUnit B w hconn hwpos
  exact (onShellEnergy_hasFDerivAt_force c B eta w hunit hwpos).continuousAt.continuousWithinAt

/-- **Theorem 2A (box existence).** `Φ` attains a minimum on `[1/3, 3]ᴱ`. -/
theorem exists_minimizer_on_adm_box (c : ℝ) (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] (hconn : IncidenceConnected B) :
    ∃ w ∈ admBox E, IsMinOn (onShellEnergy c B eta) (admBox E) w :=
  isCompact_admBox.exists_isMinOn admBox_nonempty
    (onShellEnergy_continuousOn_adm c B eta hconn)

/-- Kirchhoff current for unit weights: `y = Bᵀ M_1⁻¹ η`. -/
def kirchhoffCurrent (B : Matrix V E ℝ) (eta : V → ℝ) : E → ℝ :=
  Bᵀ.mulVec (onShellPotential B eta fun _ => 1)

omit [DecidableEq V] in
theorem weightedLap_one_mulVec (B : Matrix V E ℝ) (Psi : V → ℝ) :
    (weightedLap B fun _ => 1).mulVec Psi = B.mulVec (Bᵀ.mulVec Psi) := by
  rw [weightedLap_mulVec]
  simp

/-- Thomson: `ηᵀ M_w⁻¹ η ≤ ∑ y_e² / w_e` for the unit-weight current `y`. -/
theorem electrical_le_thomson (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (hmean : ∑ v, eta v = 0) :
    dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) ≤
      ∑ e, kirchhoffCurrent B eta e ^ 2 / w e := by
  have h1 : ∀ e : E, (0 : ℝ) < 1 := fun _ => by norm_num
  have hunit1 := shiftedWeightedLap_isUnit B (fun _ => 1) hconn h1
  have hL1 := (shiftedGreen_solves_kirchhoff B eta (fun _ => 1) hbal hunit1 hmean).1
  have hy : B.mulVec (kirchhoffCurrent B eta) = eta := by
    unfold kirchhoffCurrent
    rw [← weightedLap_one_mulVec, hL1]
  have hunitw := shiftedWeightedLap_isUnit B w hconn hw
  have hLw := (shiftedGreen_solves_kirchhoff B eta w hbal hunitw hmean).1
  have hsolve :
      (weightedLap B w).mulVec (onShellPotential B eta w) =
        B.mulVec (kirchhoffCurrent B eta) := by
    rw [hLw, hy]
  have hηΨ :
      dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) =
        dotProduct (kirchhoffCurrent B eta)
          (Bᵀ.mulVec (onShellPotential B eta w)) := by
    calc
      dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) =
          dotProduct (B.mulVec (kirchhoffCurrent B eta))
            ((shiftedWeightedLap B w)⁻¹.mulVec eta) := by rw [hy]
      _ = dotProduct (kirchhoffCurrent B eta)
            (Bᵀ.mulVec ((shiftedWeightedLap B w)⁻¹.mulVec eta)) := by
          rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
            dotProduct_comm]
      _ = dotProduct (kirchhoffCurrent B eta)
            (Bᵀ.mulVec (onShellPotential B eta w)) := by
          simp [onShellPotential]
  rw [hηΨ]
  exact transfer_matrix_loewner_le_diag_inv B w hw (onShellPotential B eta w)
    (kirchhoffCurrent B eta) hsolve

/-- **Theorem 2A (coercivity).** `Φ(w) ≥ ∑ V(w_e) - (c/2) ∑ y_e²/w_e`. -/
theorem onShellEnergy_coercive_bound (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (hmean : ∑ v, eta v = 0) :
    ∑ e, UniversalStability.V (w e) - c / 2 * ∑ e, kirchhoffCurrent B eta e ^ 2 / w e ≤
      onShellEnergy c B eta w := by
  unfold onShellEnergy
  have hQ := electrical_le_thomson B eta w hbal hconn hw hmean
  have : c / 2 * dotProduct eta ((shiftedWeightedLap B w)⁻¹.mulVec eta) ≤
      c / 2 * ∑ e, kirchhoffCurrent B eta e ^ 2 / w e :=
    mul_le_mul_of_nonneg_left hQ (div_nonneg hc (by norm_num))
  linarith

/-- Constitutive plus Thomson remainder, rewritten over a common denominator.
The `3/t²` term dominates `C/t` as `t → 0⁺`; `3(t-1)²` dominates as `t → +∞`. -/
theorem constitutive_minus_thomson (C t : ℝ) (ht : 0 < t) :
    3 * (t - 1) ^ 2 + 3 / t ^ 2 - C / t =
      3 * (t - 1) ^ 2 + (3 - C * t) / t ^ 2 := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp [ht0]
  ring

/-- Open positive orthant `Ω = ℝ_{>0}^E`. -/
def positiveOrthant (E : Type*) [Fintype E] : Set (E → ℝ) :=
  {w | ∀ e, 0 < w e}

theorem positiveOrthant_eq_pi {E : Type*} [Fintype E] :
    positiveOrthant E = Set.pi Set.univ (fun _ : E => Set.Ioi (0 : ℝ)) := by
  ext w
  constructor
  · intro hw i _
    exact hw i
  · intro hw i
    exact hw i (Set.mem_univ i)

theorem isOpen_positiveOrthant {E : Type*} [Fintype E] :
    IsOpen (positiveOrthant E) := by
  rw [positiveOrthant_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi

def coordMin {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty w

def coordMax {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w

theorem coordMin_le {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) (e : E) :
    coordMin w ≤ w e :=
  (Finset.inf'_le_iff (H := Finset.univ_nonempty) (f := w)).mpr
    ⟨e, Finset.mem_univ e, le_rfl⟩

theorem le_coordMax {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) (e : E) :
    w e ≤ coordMax w :=
  (Finset.le_sup'_iff (H := Finset.univ_nonempty) (f := w)).mpr
    ⟨e, Finset.mem_univ e, le_rfl⟩

theorem coordMin_pos {E : Type*} [Fintype E] [Nonempty E] {w : E → ℝ}
    (hw : ∀ e, 0 < w e) : 0 < coordMin w :=
  (Finset.lt_inf'_iff (H := Finset.univ_nonempty) (f := w)).mpr fun e _ => hw e

theorem thomsonConst_nonneg (B : Matrix V E ℝ) (eta : V → ℝ) :
    0 ≤ ∑ e, kirchhoffCurrent B eta e ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem thomson_le_const_div_wmin [Nonempty E] (B : Matrix V E ℝ)
    (eta : V → ℝ) (w : E → ℝ) (hw : ∀ e, 0 < w e) :
    ∑ e, kirchhoffCurrent B eta e ^ 2 / w e ≤
      (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
  have hmin : 0 < coordMin w := coordMin_pos hw
  have hterm : ∀ e, kirchhoffCurrent B eta e ^ 2 / w e ≤
      kirchhoffCurrent B eta e ^ 2 / coordMin w := fun e =>
    div_le_div_of_nonneg_left (sq_nonneg _) hmin (coordMin_le w e)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun e _ => hterm e
  have hfactor :
      ∑ e, kirchhoffCurrent B eta e ^ 2 / coordMin w =
        (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
    simp_rw [div_eq_inv_mul, ← Finset.mul_sum]
  rwa [hfactor] at hsum

omit [DecidableEq E] in
theorem sumV_ge_single (w : E → ℝ) (hw : ∀ e, 0 < w e) (e0 : E) :
    UniversalStability.V (w e0) ≤ ∑ e, UniversalStability.V (w e) :=
  Finset.single_le_sum (fun e _ =>
      le_trans (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (w e)))
        (V_ge_three_inv_sq (hw e)))
    (Finset.mem_univ e0)

/-- `Φ(w) ≥ 3 / w_min² - (c/2) C_η / w_min`. -/
theorem onShellEnergy_ge_wmin_blowup (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (hmean : ∑ v, eta v = 0) :
    3 / (coordMin w) ^ 2 -
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w ≤
      onShellEnergy c B eta w := by
  have hbound := onShellEnergy_coercive_bound c hc B eta w hbal hconn hw hmean
  obtain ⟨e0, _, he0⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty w
  have hV : 3 / (coordMin w) ^ 2 ≤ ∑ e, UniversalStability.V (w e) := by
    have hone := V_ge_three_inv_sq (hw e0)
    have hle := le_trans hone (sumV_ge_single w hw e0)
    have hcm : coordMin w = w e0 := by
      simpa [coordMin] using
        (congr_arg (fun H : Finset.univ.Nonempty => Finset.univ.inf' H w)
          (Subsingleton.elim Finset.univ_nonempty ⟨e0, Finset.mem_univ e0⟩)).trans
          he0
    rwa [hcm]
  have hTh := thomson_le_const_div_wmin B eta w hw
  have hC :
      c / 2 * ∑ e, kirchhoffCurrent B eta e ^ 2 / w e ≤
        c / 2 * ((∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w) :=
    mul_le_mul_of_nonneg_left hTh (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 2))
  have hC' :
      c / 2 * ((∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w) =
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
    ring
  linarith [hbound, hV, hC, hC']

/-- `Φ(w) ≥ 3(w_max-1)² - (c/2) C_η / w_min`. -/
theorem onShellEnergy_ge_wmax_blowup (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hw : ∀ e, 0 < w e) (hmean : ∑ v, eta v = 0) :
    3 * (coordMax w - 1) ^ 2 -
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w ≤
      onShellEnergy c B eta w := by
  have hbound := onShellEnergy_coercive_bound c hc B eta w hbal hconn hw hmean
  obtain ⟨e0, _, he0⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty w
  have hV : 3 * (coordMax w - 1) ^ 2 ≤ ∑ e, UniversalStability.V (w e) := by
    have hone := (V_coercive_coords (hw e0)).2
    have hle := le_trans hone (sumV_ge_single w hw e0)
    have hcm : coordMax w = w e0 := by
      simpa [coordMax] using
        (congr_arg (fun H : Finset.univ.Nonempty => Finset.univ.sup' H w)
          (Subsingleton.elim Finset.univ_nonempty ⟨e0, Finset.mem_univ e0⟩)).trans
          he0
    rwa [hcm]
  have hTh := thomson_le_const_div_wmin B eta w hw
  have hC :
      c / 2 * ∑ e, kirchhoffCurrent B eta e ^ 2 / w e ≤
        c / 2 * ((∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w) :=
    mul_le_mul_of_nonneg_left hTh (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 2))
  have hC' :
      c / 2 * ((∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w) =
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
    ring
  linarith [hbound, hV, hC, hC']

/-- Thresholds: `3/t² - C/t > M` for `0 < t < ε`, and the `w_max` comparison. -/
theorem exists_coercive_thresholds (C M : ℝ) (hC : 0 ≤ C) :
    ∃ ε R : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ R ∧
      (∀ t : ℝ, 0 < t → t < ε → M < 3 / t ^ 2 - C / t) ∧
      M < 3 * (R - 1) ^ 2 - C / ε := by
  let K : ℝ := 1 + C + |M|
  have hKpos : 0 < K := by
    linarith [abs_nonneg M]
  have hKge : (1 : ℝ) ≤ K := by
    linarith [abs_nonneg M]
  let ε : ℝ := 1 / K
  have hεpos : 0 < ε := div_pos (by norm_num) hKpos
  have hεle : ε ≤ 1 := (div_le_one hKpos).mpr hKge
  have hCε : C * ε < 1 := by
    have hmul : C * ε = C / K := by
      simp [ε, div_eq_mul_inv]
    rw [hmul, div_lt_one hKpos]
    linarith [abs_nonneg M]
  have hfε : M < 3 / ε ^ 2 - C / ε := by
    have hne : ε ≠ 0 := ne_of_gt hεpos
    have hrew : 3 / ε ^ 2 - C / ε = (3 - C * ε) / ε ^ 2 := by
      field_simp [hne]
    rw [hrew]
    have hε2 : 0 < ε ^ 2 := pow_pos hεpos 2
    have hnum : (2 : ℝ) < 3 - C * ε := by linarith
    have h2 : (2 : ℝ) / ε ^ 2 < (3 - C * ε) / ε ^ 2 :=
      (div_lt_div_iff_of_pos_right hε2).mpr hnum
    have h2eq : (2 : ℝ) / ε ^ 2 = 2 * K ^ 2 := by
      have : ε ^ 2 = (1 / K) ^ 2 := rfl
      rw [this, div_pow, one_pow]
      field_simp [ne_of_gt hKpos]
    have hMK : M ≤ 2 * K ^ 2 := by
      have hKsq : K ≤ K ^ 2 := by nlinarith [hKge]
      have : M ≤ |M| := le_abs_self M
      have : |M| ≤ K := by
        simp only [K]
        linarith [abs_nonneg M]
      nlinarith
    linarith
  have hsmall : ∀ t : ℝ, 0 < t → t < ε → M < 3 / t ^ 2 - C / t := by
    intro t ht htε
    have hεt : 0 < ε - t := sub_pos.mpr htε
    have hne : t ≠ 0 := ne_of_gt ht
    have hε0 : ε ≠ 0 := ne_of_gt hεpos
    have hdiff :
        (3 / t ^ 2 - C / t) - (3 / ε ^ 2 - C / ε) =
          (ε - t) / (t * ε) * (3 * (ε + t) / (t * ε) - C) := by
      field_simp [hne, hε0]
      ring
    have hfac : 0 < (ε - t) / (t * ε) :=
      div_pos hεt (mul_pos ht hεpos)
    have hbrac : 0 < 3 * (ε + t) / (t * ε) - C := by
      have h3 : (3 : ℝ) / t < 3 * (ε + t) / (t * ε) := by
        have : (3 : ℝ) / t = 3 * ε / (t * ε) := by
          field_simp [hne, hε0]
        rw [this]
        have : 0 < t * ε := mul_pos ht hεpos
        exact div_lt_div_of_pos_right (by linarith) this
      have : (3 : ℝ) / ε < 3 / t :=
        div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) ht htε
      have : C < 3 / ε := by
        have : C * ε < 1 := hCε
        have : C < 1 / ε := (lt_div_iff₀ hεpos).mpr (by linarith)
        have : (1 : ℝ) / ε < 3 / ε :=
          div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 3) hεpos
        linarith
      linarith
    have : 0 < (3 / t ^ 2 - C / t) - (3 / ε ^ 2 - C / ε) := by
      rw [hdiff]
      exact mul_pos hfac hbrac
    linarith [hfε]
  let T : ℝ := |M| + C / ε + 1
  have hTpos : 0 < T := by
    have : 0 ≤ C / ε := div_nonneg hC (le_of_lt hεpos)
    linarith [abs_nonneg M]
  let R : ℝ := 1 + Real.sqrt (T / 3)
  have hRge : (1 : ℝ) ≤ R := by
    linarith [Real.sqrt_nonneg (T / 3)]
  have hfR : M < 3 * (R - 1) ^ 2 - C / ε := by
    have hR1 : R - 1 = Real.sqrt (T / 3) := by simp [R]
    have hsq : 3 * (R - 1) ^ 2 = T := by
      have hnn : 0 ≤ T / 3 := div_nonneg (le_of_lt hTpos) (by norm_num)
      rw [hR1, Real.sq_sqrt hnn]
      ring
    have : 3 * (R - 1) ^ 2 - C / ε = |M| + 1 := by
      rw [hsq]
      simp [T]
      ring
    linarith [le_abs_self M]
  exact ⟨ε, R, hεpos, hεle, hRge, hsmall, hfR⟩

def closedWeightBox {E : Type*} [Fintype E] (ε R : ℝ) : Set (E → ℝ) :=
  {w | ∀ e, ε ≤ w e ∧ w e ≤ R}

theorem closedWeightBox_eq_pi {E : Type*} [Fintype E] (ε R : ℝ) :
    closedWeightBox (E := E) ε R =
      Set.pi Set.univ (fun _ : E => Set.Icc ε R) := by
  ext w
  constructor
  · intro hw i _
    exact ⟨(hw i).1, (hw i).2⟩
  · intro hw i
    exact hw i (Set.mem_univ i)

theorem isCompact_closedWeightBox {E : Type*} [Fintype E] (ε R : ℝ) :
    IsCompact (closedWeightBox (E := E) ε R) := by
  rw [closedWeightBox_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem not_mem_closedWeightBox_iff {E : Type*} [Fintype E] [Nonempty E]
    {ε R : ℝ} {w : E → ℝ} :
    w ∉ closedWeightBox (E := E) ε R ↔ coordMin w < ε ∨ R < coordMax w := by
  constructor
  · intro h
    have : ∃ e, ¬(ε ≤ w e ∧ w e ≤ R) := by
      rw [closedWeightBox, Set.mem_setOf_eq, not_forall] at h
      exact h
    obtain ⟨e, he⟩ := this
    rw [not_and_or, not_le, not_le] at he
    rcases he with hε | hR
    · left
      exact (Finset.inf'_lt_iff (H := Finset.univ_nonempty) (f := w)).mpr
        ⟨e, Finset.mem_univ e, hε⟩
    · right
      exact (Finset.lt_sup'_iff (H := Finset.univ_nonempty) (f := w)).mpr
        ⟨e, Finset.mem_univ e, hR⟩
  · intro h hw
    rcases h with hε | hR
    · obtain ⟨e, _, he⟩ :=
        (Finset.inf'_lt_iff (H := Finset.univ_nonempty) (f := w)).mp hε
      exact (not_le.mpr he) (hw e).1
    · obtain ⟨e, _, he⟩ :=
        (Finset.lt_sup'_iff (H := Finset.univ_nonempty) (f := w)).mp hR
      exact (not_le.mpr he) (hw e).2

theorem onShellEnergy_continuousOn_box (c : ℝ) (B : Matrix V E ℝ)
    (eta : V → ℝ) [Nonempty V] (hconn : IncidenceConnected B)
    {ε R : ℝ} (hε : 0 < ε) :
    ContinuousOn (onShellEnergy c B eta) (closedWeightBox (E := E) ε R) := by
  intro w hw
  have hwpos : ∀ e, 0 < w e := fun e => lt_of_lt_of_le hε (hw e).1
  have hunit := shiftedWeightedLap_isUnit B w hconn hwpos
  exact (onShellEnergy_hasFDerivAt_force c B eta w hunit hwpos).continuousAt.continuousWithinAt

/-- **Theorem 2A (coercivity).** `Φ(w) → +∞` as `w_min → 0⁺` or `w_max → +∞`. -/
theorem onShellEnergy_coercive_thresholds (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (M : ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) :
    ∃ ε R : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ R ∧
      ∀ w, w ∈ positiveOrthant E →
        (coordMin w < ε ∨ R < coordMax w) →
          M < onShellEnergy c B eta w := by
  let C : ℝ := c / 2 * ∑ e, kirchhoffCurrent B eta e ^ 2
  have hC : 0 ≤ C :=
    mul_nonneg (div_nonneg hc (by norm_num)) (thomsonConst_nonneg B eta)
  obtain ⟨ε, R, hε, hε1, hR, hsmall, hbig⟩ := exists_coercive_thresholds C M hC
  refine ⟨ε, R, hε, hε1, hR, ?_⟩
  intro w hw hbd
  have hwpos : ∀ e, 0 < w e := hw
  by_cases hmin : coordMin w < ε
  · have hge := onShellEnergy_ge_wmin_blowup c hc B eta w hbal hconn hwpos hmean
    have hCeq : C / coordMin w =
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
      simp [C]
    have : M < 3 / (coordMin w) ^ 2 - C / coordMin w :=
      hsmall (coordMin w) (coordMin_pos hwpos) hmin
    linarith
  · have hmax : R < coordMax w := hbd.resolve_left hmin
    have hwmin : ε ≤ coordMin w := le_of_not_gt hmin
    have hge := onShellEnergy_ge_wmax_blowup c hc B eta w hbal hconn hwpos hmean
    have hminpos : 0 < coordMin w := coordMin_pos hwpos
    have hCdiv : C / coordMin w ≤ C / ε :=
      div_le_div_of_nonneg_left hC hε hwmin
    have hwmax1 : 0 ≤ R - 1 := sub_nonneg.mpr hR
    have hsq : 3 * (R - 1) ^ 2 < 3 * (coordMax w - 1) ^ 2 := by
      have : 0 ≤ coordMax w - 1 := by
        have : (1 : ℝ) ≤ R := hR
        linarith
      have hmon : R - 1 < coordMax w - 1 := by linarith
      have := pow_lt_pow_left₀ hmon hwmax1 (by norm_num : (2 : ℕ) ≠ 0)
      nlinarith
    have hCeq : C / coordMin w =
        c / 2 * (∑ e, kirchhoffCurrent B eta e ^ 2) / coordMin w := by
      simp [C]
    linarith

/-- **Theorem 2A (existence on `Ω`).** A continuous coercive `Φ` attains a
global minimizer in the open orthant, which is an on-shell equilibrium. -/
theorem exists_minimizer_on_orthant (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) :
    ∃ w ∈ positiveOrthant E,
      IsMinOn (onShellEnergy c B eta) (positiveOrthant E) w := by
  let ones : E → ℝ := fun _ => 1
  have hones : ones ∈ positiveOrthant E := fun _ => by norm_num
  let M : ℝ := onShellEnergy c B eta ones
  obtain ⟨ε, R, hε, hε1, hR, hblow⟩ :=
    onShellEnergy_coercive_thresholds c hc B eta M hbal hconn hmean
  have hbox_nonempty : (closedWeightBox (E := E) ε R).Nonempty :=
    ⟨ones, fun _ => ⟨hε1, hR⟩⟩
  have hcont :=
    onShellEnergy_continuousOn_box (ε := ε) (R := R) c B eta hconn hε
  obtain ⟨w, hwbox, hmin⟩ :=
    (isCompact_closedWeightBox ε R).exists_isMinOn hbox_nonempty hcont
  have hwΩ : w ∈ positiveOrthant E := fun e =>
    lt_of_lt_of_le hε (hwbox e).1
  refine ⟨w, hwΩ, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  by_cases hybox : y ∈ closedWeightBox (E := E) ε R
  · exact (isMinOn_iff.mp hmin) y hybox
  · have hbd : coordMin y < ε ∨ R < coordMax y :=
      (not_mem_closedWeightBox_iff).mp hybox
    have hMlt : M < onShellEnergy c B eta y := hblow y hy hbd
    have honesBox : ones ∈ closedWeightBox (E := E) ε R :=
      fun _ => ⟨hε1, hR⟩
    have hwle : onShellEnergy c B eta w ≤ M :=
      (isMinOn_iff.mp hmin) ones honesBox
    exact le_of_lt (lt_of_le_of_lt hwle hMlt)

theorem exists_minimizer_on_orthant_force_zero (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) :
    ∃ w ∈ positiveOrthant E,
      IsMinOn (onShellEnergy c B eta) (positiveOrthant E) w ∧
        onShellForceOnShell c B eta w = 0 := by
  obtain ⟨w, hw, hmin⟩ :=
    exists_minimizer_on_orthant c hc B eta hbal hconn hmean
  have hwpos : ∀ e, 0 < w e := hw
  have hunit := shiftedWeightedLap_isUnit B w hconn hwpos
  have hloc : IsLocalMin (onShellEnergy c B eta) w :=
    hmin.filter_mono <| Filter.le_principal_iff.mpr <|
      IsOpen.mem_nhds isOpen_positiveOrthant hw
  refine ⟨w, hw, hmin, localMin_force_zero c B eta w hunit hwpos hloc⟩

/-- **Theorem 2A (compact sublevels).** `{w ∈ Ω : Φ(w) ≤ K}` is compact in `Ω`. -/
theorem isCompact_onShellEnergy_sublevel (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (K : ℝ)
    [Nonempty V] [Nonempty E]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hmean : ∑ v, eta v = 0) :
    IsCompact {w | w ∈ positiveOrthant E ∧ onShellEnergy c B eta w ≤ K} := by
  obtain ⟨ε, R, hε, hε1, hR, hblow⟩ :=
    onShellEnergy_coercive_thresholds c hc B eta K hbal hconn hmean
  let s := closedWeightBox (E := E) ε R
  have hs : IsCompact s := isCompact_closedWeightBox ε R
  have hboxΩ : s ⊆ positiveOrthant E :=
    fun w hw e => lt_of_lt_of_le hε (hw e).1
  have hS :
      {w | w ∈ positiveOrthant E ∧ onShellEnergy c B eta w ≤ K} =
        {w | w ∈ s ∧ onShellEnergy c B eta w ≤ K} := by
    ext w
    constructor
    · intro ⟨hwΩ, hΦ⟩
      refine ⟨?_, hΦ⟩
      by_contra hbox
      exact (not_le_of_gt (hblow w hwΩ (not_mem_closedWeightBox_iff.mp hbox))) hΦ
    · intro ⟨hwbox, hΦ⟩
      exact ⟨hboxΩ hwbox, hΦ⟩
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hct : Continuous (s.restrict (onShellEnergy c B eta)) :=
    continuousOn_iff_continuous_restrict.mp
      (onShellEnergy_continuousOn_box (ε := ε) (R := R) c B eta hconn hε)
  have hcl : IsClosed {w : s | onShellEnergy c B eta w.1 ≤ K} :=
    isClosed_le hct continuous_const
  have hcp : IsCompact {w : s | onShellEnergy c B eta w.1 ≤ K} :=
    hcl.isCompact
  have himg :
      Subtype.val '' {w : s | onShellEnergy c B eta w.1 ≤ K} =
        {w | w ∈ s ∧ onShellEnergy c B eta w ≤ K} := by
    ext w
    constructor
    · intro hw
      rcases (Set.mem_image _ _ _).mp hw with ⟨⟨x, hx⟩, hxK, hval⟩
      subst hval
      exact ⟨hx, hxK⟩
    · intro ⟨hw, hK⟩
      exact ⟨⟨w, hw⟩, hK, rfl⟩
  rw [hS, ← himg]
  exact hcp.image continuous_subtype_val

end UniversalStability
