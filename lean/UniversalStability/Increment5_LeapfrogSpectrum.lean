import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

import UniversalStability.Increment1_HessianSpectrum
import UniversalStability.Increment2_BlockDecoupling
import UniversalStability.Increment3_SteinLyapunov
import UniversalStability.Theorem3

/-!
# Increment (v) — spectrum of `leapfrogLin(diag λ)` via invariant 2-planes

The operator acts independently on each coordinate pair `(u_i, v_i)`, so
`spec_ℂ(leapfrogLin(diag λ)) = ⋃_i spec_ℂ(J_{λ_i})`. Combined with
orthogonal conjugation this yields `ρ(𝒥) < 1` on the Jury range.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Polynomial

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem ofRealMat_diagonal (lam : E → ℝ) :
    ofRealMat (diagonal lam) = diagonal fun i => (lam i : ℂ) := by
  ext i j
  simp [ofRealMat, Matrix.map_apply, diagonal]
  split_ifs <;> simp

theorem ofRealMat_leapfrogLin (γ ΔT : ℝ) (H : Matrix E E ℝ) :
    ofRealMat (leapfrogLin γ ΔT H) =
      fromBlocks (1 : Matrix E E ℂ) ((ΔT : ℂ) • 1)
        ((-(ΔT : ℂ)) • ofRealMat H)
        ((1 - γ * ΔT : ℂ) • 1 - (ΔT : ℂ) ^ 2 • ofRealMat H) := by
  unfold ofRealMat leapfrogLin
  rw [fromBlocks_map]
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp [fromBlocks, one_apply]
    | inr j =>
      simp [fromBlocks, smul_apply, one_apply]
      split_ifs <;> simp
  | inr i =>
    cases y with
    | inl j =>
      simp [fromBlocks, smul_apply, neg_smul]
    | inr j =>
      simp [fromBlocks, sub_apply, smul_apply, one_apply, pow_two]
      split_ifs <;> simp

/-- Standard embedding of a 2-vector into the `k`-th invariant plane. -/
def pairEmbed (k : E) (α β : ℂ) : E ⊕ E → ℂ :=
  Sum.elim (Pi.single k α) (Pi.single k β)

theorem pairEmbed_eq_zero_iff (k : E) (α β : ℂ) :
    pairEmbed k α β = 0 ↔ α = 0 ∧ β = 0 := by
  constructor
  · intro h
    constructor
    · have := congrFun h (Sum.inl k)
      simpa [pairEmbed, Pi.single_eq_same] using this
    · have := congrFun h (Sum.inr k)
      simpa [pairEmbed, Pi.single_eq_same] using this
  · rintro ⟨rfl, rfl⟩
    ext x
    cases x with
    | inl i => simp [pairEmbed]
    | inr i => simp [pairEmbed]

theorem modeBlock_map_mulVec (γ ΔT eig : ℝ) (α β : ℂ) :
    (ofRealMat (modeBlock γ ΔT eig)).mulVec ![α, β] =
      ![α + ΔT * β,
        -ΔT * eig * α + (1 - γ * ΔT - eig * ΔT ^ 2) * β] := by
  ext i
  fin_cases i <;>
    simp [ofRealMat, modeBlock, mulVec, dotProduct, Fin.sum_univ_two]

/-- Coordinate action of the complexified leapfrog operator on `diag λ`. -/
theorem leapfrogLin_map_mulVec_coord (γ ΔT : ℝ) (lam : E → ℝ)
    (z : E ⊕ E → ℂ) (i : E) :
    let A := ofRealMat (leapfrogLin γ ΔT (diagonal lam))
    A.mulVec z (Sum.inl i) = z (Sum.inl i) + ΔT * z (Sum.inr i) ∧
      A.mulVec z (Sum.inr i) =
        -ΔT * lam i * z (Sum.inl i) +
          (1 - γ * ΔT - lam i * ΔT ^ 2) * z (Sum.inr i) := by
  intro A
  have hA : A =
      fromBlocks (1 : Matrix E E ℂ) ((ΔT : ℂ) • 1)
        ((-(ΔT : ℂ)) • ofRealMat (diagonal lam))
        ((1 - γ * ΔT : ℂ) • 1 - (ΔT : ℂ) ^ 2 • ofRealMat (diagonal lam)) :=
    ofRealMat_leapfrogLin γ ΔT (diagonal lam)
  have hdiag : ofRealMat (diagonal lam) = diagonal fun j => (lam j : ℂ) :=
    ofRealMat_diagonal lam
  constructor
  · rw [hA, fromBlocks_mulVec]
    simp [one_mulVec, smul_mulVec]
  · rw [hA, fromBlocks_mulVec]
    have hΛu :
        ((-(ΔT : ℂ) • ofRealMat (diagonal lam)).mulVec (z ∘ Sum.inl)) i =
          -((ΔT : ℂ) * (lam i : ℂ) * z (Sum.inl i)) := by
      rw [smul_mulVec, hdiag]
      simp [Pi.smul_apply, mulVec_diagonal]
      ring
    have hDu :
        ((((1 - γ * ΔT : ℂ) • (1 : Matrix E E ℂ) -
            (ΔT : ℂ) ^ 2 • ofRealMat (diagonal lam)).mulVec (z ∘ Sum.inr)) i) =
          (1 - γ * ΔT) * z (Sum.inr i) - (ΔT : ℂ) ^ 2 * (lam i : ℂ) * z (Sum.inr i) := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, smul_mulVec, hdiag]
      simp [Pi.sub_apply, Pi.smul_apply, mulVec_diagonal]
      ring
    trans
      (((-(ΔT : ℂ) • ofRealMat (diagonal lam)).mulVec (z ∘ Sum.inl) +
          (((1 - γ * ΔT : ℂ) • 1 -
              (ΔT : ℂ) ^ 2 • ofRealMat (diagonal lam)).mulVec (z ∘ Sum.inr))) i)
    · rfl
    · rw [Pi.add_apply, hΛu, hDu]
      ring

theorem leapfrogLin_map_mulVec_pairEmbed (γ ΔT : ℝ) (lam : E → ℝ)
    (k : E) (α β : ℂ) :
    (ofRealMat (leapfrogLin γ ΔT (diagonal lam))).mulVec (pairEmbed k α β) =
      pairEmbed k
        ((ofRealMat (modeBlock γ ΔT (lam k))).mulVec ![α, β] 0)
        ((ofRealMat (modeBlock γ ΔT (lam k))).mulVec ![α, β] 1) := by
  funext x
  have hmode := modeBlock_map_mulVec γ ΔT (lam k) α β
  cases x with
  | inl i =>
    have hcoord := (leapfrogLin_map_mulVec_coord γ ΔT lam (pairEmbed k α β) i).1
    rw [hcoord]
    by_cases hik : k = i
    · subst hik
      simp [pairEmbed, Pi.single_eq_same, hmode]
    ·       simp [pairEmbed, hik]
  | inr i =>
    have hcoord := (leapfrogLin_map_mulVec_coord γ ΔT lam (pairEmbed k α β) i).2
    rw [hcoord]
    by_cases hik : k = i
    · subst hik
      simp [pairEmbed, Pi.single_eq_same, hmode]
    · simp [pairEmbed, hik]

theorem mem_spectrum_ofRealMat_iff {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (ofRealMat A) ↔ IsRoot (A.charpoly.map Complex.ofRealHom) μ := by
  rw [ofRealMat, mem_spectrum_iff_isRoot_charpoly, charpoly_map]

theorem mem_spectrum_modeBlock_iff (γ ΔT eig : ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (ofRealMat (modeBlock γ ΔT eig)) ↔
      ((modeBlock γ ΔT eig).charpoly.map Complex.ofRealHom).eval μ = 0 := by
  rw [mem_spectrum_ofRealMat_iff, IsRoot.def]

theorem mem_spectrum_iff_exists_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ z ≠ 0, A.mulVec z = μ • z := by
  have hdiag : μ • (1 : Matrix n n ℂ) = diagonal fun _ => μ := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [smul_apply, diagonal]
    · simp [smul_apply, diagonal, h]
  have hdet : μ ∈ spectrum ℂ A ↔ (μ • (1 : Matrix n n ℂ) - A).det = 0 := by
    rw [mem_spectrum_iff_isRoot_charpoly, IsRoot.def, eval_charpoly, hdiag]
    simp
  rw [hdet, ← exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨z, hz0, hz⟩
    refine ⟨z, hz0, ?_⟩
    have : (μ • (1 : Matrix n n ℂ)).mulVec z - A.mulVec z = 0 := by
      simpa [sub_mulVec] using hz
    have hμ : (μ • (1 : Matrix n n ℂ)).mulVec z = μ • z := by
      simp [smul_mulVec, one_mulVec]
    have h' : μ • z - A.mulVec z = 0 := by simpa [hμ] using this
    exact (sub_eq_zero.mp h').symm
  · rintro ⟨z, hz0, hz⟩
    refine ⟨z, hz0, ?_⟩
    simp [sub_mulVec, smul_mulVec, one_mulVec, hz]

/-- Direct spectrum equivalence: invariant 2-planes exhaust
`spec_ℂ(leapfrogLin(diag λ))`. -/
theorem spec_leapfrogLin_diag (γ ΔT : ℝ) (lam : E → ℝ) :
    spectrum ℂ (ofRealMat (leapfrogLin γ ΔT (diagonal lam))) =
      ⋃ i : E, spectrum ℂ (ofRealMat (modeBlock γ ΔT (lam i))) := by
  ext μ
  constructor
  · intro hμ
    obtain ⟨z, hz0, hz⟩ := (mem_spectrum_iff_exists_mulVec _ μ).mp hμ
    have hex : ∃ k : E, ¬ (z (Sum.inl k) = 0 ∧ z (Sum.inr k) = 0) := by
      by_contra hnone
      push_neg at hnone
      apply hz0
      ext x
      cases x with
      | inl i => exact (hnone i).1
      | inr i => exact (hnone i).2
    obtain ⟨k, hk⟩ := hex
    have hw : (![z (Sum.inl k), z (Sum.inr k)] : Fin 2 → ℂ) ≠ 0 := by
      intro hw0
      have h0 : z (Sum.inl k) = 0 ∧ z (Sum.inr k) = 0 := by
        constructor
        · simpa using congrFun hw0 0
        · simpa using congrFun hw0 1
      exact hk h0
    have hJk :
        (ofRealMat (modeBlock γ ΔT (lam k))).mulVec
            ![z (Sum.inl k), z (Sum.inr k)] =
          μ • ![z (Sum.inl k), z (Sum.inr k)] := by
      ext i
      have hcoord := leapfrogLin_map_mulVec_coord γ ΔT lam z k
      have hzμ := congrFun hz
      fin_cases i
      · have := hzμ (Sum.inl k)
        simp [hcoord.1, Pi.smul_apply, smul_eq_mul] at this ⊢
        simp [modeBlock_map_mulVec, this]
      · have := hzμ (Sum.inr k)
        simp [hcoord.2, Pi.smul_apply, smul_eq_mul] at this ⊢
        simp [modeBlock_map_mulVec, this]
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    exact (mem_spectrum_iff_exists_mulVec _ μ).mpr ⟨_, hw, hJk⟩
  · intro hμ
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hμ
    obtain ⟨w, hw0, hw⟩ := (mem_spectrum_iff_exists_mulVec _ μ).mp hk
    set α := w 0
    set β := w 1
    have hwab : w = ![α, β] := by
      ext i
      fin_cases i <;> simp [α, β]
    have hz :
        (ofRealMat (leapfrogLin γ ΔT (diagonal lam))).mulVec (pairEmbed k α β) =
          μ • pairEmbed k α β := by
      rw [leapfrogLin_map_mulVec_pairEmbed, ← hwab, hw]
      ext x
      cases x with
      | inl i =>
        by_cases hik : k = i
        · subst hik
          simp [pairEmbed, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, α]
        ·           simp [pairEmbed, Pi.single_apply, Pi.smul_apply,
            if_neg (Ne.symm hik)]
      | inr i =>
        by_cases hik : k = i
        · subst hik
          simp [pairEmbed, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, β]
        · simp [pairEmbed, Pi.single_apply, Pi.smul_apply,
            if_neg (Ne.symm hik)]
    have hz0 : pairEmbed k α β ≠ 0 := by
      intro h0
      have := (pairEmbed_eq_zero_iff k α β).mp h0
      apply hw0
      rw [hwab]
      ext i
      fin_cases i <;> simp [this]
    exact (mem_spectrum_iff_exists_mulVec _ μ).mpr ⟨_, hz0, hz⟩

open scoped Matrix.Norms.L2Operator

theorem spectralRadius_leapfrogLin_diag_lt_one [Nonempty E]
    (lam : E → ℝ) (ΔT : ℝ) (hpos : ∀ i, 0 < lam i) (hbd : ∀ i, lam i ≤ 1464)
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    spectralRadius ℂ (ofRealMat (leapfrogLin 3 ΔT (diagonal lam))) < 1 := by
  have hspec := spec_leapfrogLin_diag 3 ΔT lam
  refine spectrum.spectralRadius_lt_of_forall_lt
      (ofRealMat (leapfrogLin 3 ΔT (diagonal lam))) ?_
  intro μ hμ
  have : μ ∈ ⋃ i : E, spectrum ℂ (ofRealMat (modeBlock 3 ΔT (lam i))) := by
    rwa [← hspec]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
  have hroot : ((modeBlock 3 ΔT (lam i)).charpoly.map Complex.ofRealHom).eval μ = 0 :=
    (mem_spectrum_modeBlock_iff 3 ΔT (lam i) μ).mp hi
  have hJ : JuryStable 3 ΔT (lam i) :=
    theorem3_jury (lam i) ΔT (hpos i) (hbd i) hΔT hstep
  have hnorm : ‖μ‖ < 1 :=
    modeBlock_complex_root_norm_lt_one 3 ΔT (lam i) μ (hpos i) (ne_of_gt hΔT) hJ hroot
  exact hnorm

theorem ofRealMat_leapfrogChangeOfBasis (Q : Matrix E E ℝ) :
    ofRealMat (leapfrogChangeOfBasis Q) =
      fromBlocks (ofRealMat Q) 0 0 (ofRealMat Q) := by
  simp [ofRealMat, leapfrogChangeOfBasis, fromBlocks_map]

theorem ofRealMat_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (h : A * B = 1) :
    ofRealMat A * ofRealMat B = 1 := by
  rw [← ofRealMat_mul, h, ofRealMat_one]

theorem ofRealMat_isUnit_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hAB : A * B = 1) (hBA : B * A = 1) :
    IsUnit (ofRealMat A) :=
  ⟨⟨ofRealMat A, ofRealMat B, ofRealMat_mul_eq_one hAB, ofRealMat_mul_eq_one hBA⟩, rfl⟩

/-- Orthogonal conjugation preserves the complex spectrum of the leapfrog linearization. -/
theorem spec_leapfrogLin_conj (γ ΔT : ℝ) (H Q : Matrix E E ℝ) (hQ : Qᵀ * Q = 1)
    (hQT : Q * Qᵀ = 1) :
    spectrum ℂ (ofRealMat (leapfrogLin γ ΔT H)) =
      spectrum ℂ (ofRealMat (leapfrogLin γ ΔT (Qᵀ * H * Q))) := by
  have hconj := leapfrogLin_conj γ ΔT H Q hQ
  have hS : ofRealMat (leapfrogChangeOfBasis Q) *
      ofRealMat (leapfrogChangeOfBasis Qᵀ) = 1 := by
    rw [← ofRealMat_mul, leapfrogChangeOfBasis_mul, hQT, leapfrogChangeOfBasis_one,
      ofRealMat_one]
  have hST : ofRealMat (leapfrogChangeOfBasis Qᵀ) *
      ofRealMat (leapfrogChangeOfBasis Q) = 1 := by
    rw [← ofRealMat_mul, leapfrogChangeOfBasis_mul, hQ, leapfrogChangeOfBasis_one,
      ofRealMat_one]
  let u : (Matrix (E ⊕ E) (E ⊕ E) ℂ)ˣ :=
    ⟨ofRealMat (leapfrogChangeOfBasis Q), ofRealMat (leapfrogChangeOfBasis Qᵀ), hS, hST⟩
  have hform :
      ofRealMat (leapfrogLin γ ΔT (Qᵀ * H * Q)) =
        u⁻¹ * ofRealMat (leapfrogLin γ ΔT H) * u := by
    have hSTeq : (leapfrogChangeOfBasis Q)ᵀ = leapfrogChangeOfBasis Qᵀ :=
      leapfrogChangeOfBasis_transpose Q
    calc
      ofRealMat (leapfrogLin γ ΔT (Qᵀ * H * Q)) =
          ofRealMat ((leapfrogChangeOfBasis Q)ᵀ * leapfrogLin γ ΔT H *
            leapfrogChangeOfBasis Q) := by rw [← hconj]
      _ = ofRealMat (leapfrogChangeOfBasis Qᵀ) * ofRealMat (leapfrogLin γ ΔT H) *
            ofRealMat (leapfrogChangeOfBasis Q) := by
          rw [hSTeq, ofRealMat_mul, ofRealMat_mul]
      _ = u⁻¹ * ofRealMat (leapfrogLin γ ΔT H) * u := rfl
  rw [hform, spectrum.units_conjugate']

/-- **Theorem 4 (kernel, spectral radius).** On the Jury range, `ρ(𝒥) < 1`. -/
theorem theorem4_spectralRadius_lt_one (c : ℝ) (hc : 0 ≤ c) (ΔT : ℝ)
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty E]
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w))
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    let H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
      (Bᵀ.mulVec (onShellPotential B eta w))
    spectralRadius ℂ (ofRealMat (leapfrogLin 3 ΔT H)) < 1 := by
  intro H
  let hH := onShellHessianC_shifted_isHermitian c B w
    (Bᵀ.mulVec (onShellPotential B eta w))
  let Q := (hH.eigenvectorUnitary : Matrix E E ℝ)
  have hstar : star Q = Qᵀ := eigenvectorUnitary_star_eq_transpose hH
  have hQQ : Qᵀ * Q = 1 := by
    rw [← hstar]
    exact eigenvectorUnitary_star_mul hH
  have hQT : Q * Qᵀ = 1 := by
    rw [← hstar]
    exact eigenvectorUnitary_mul_star hH
  have hdiag : Qᵀ * H * Q = diagonal hH.eigenvalues := by
    simpa [H] using hessian_conj_is_diagonal c B w
      (Bᵀ.mulVec (onShellPotential B eta w))
  have heig0 : ∀ i, 0 < hH.eigenvalues i := fun i =>
    lt_of_lt_of_le
      (lt_trans (by norm_num : (0 : ℝ) < 10) universalFloor_gt_ten)
      (hessian_eigenvalues_mem_interval c hc B eta w hbal hconn hadm hF i).1
  have heigbd : ∀ i, hH.eigenvalues i ≤ 1464 := fun i =>
    (hessian_eigenvalues_mem_interval c hc B eta w hbal hconn hadm hF i).2
  have hρdiag :=
    spectralRadius_leapfrogLin_diag_lt_one hH.eigenvalues ΔT heig0 heigbd hΔT hstep
  have hspec := spec_leapfrogLin_conj 3 ΔT H Q hQQ hQT
  rw [hdiag] at hspec
  have : spectralRadius ℂ (ofRealMat (leapfrogLin 3 ΔT H)) =
      spectralRadius ℂ (ofRealMat (leapfrogLin 3 ΔT (diagonal hH.eigenvalues))) := by
    simp [spectralRadius, hspec]
  rwa [this]

/-- **Theorem 4 (kernel, Stein Lyapunov).** `ρ(𝒥)<1` yields a positive-definite
Stein solution with `AᵀPA−P=−I` and floor `xᵀx ≤ xᵀPx`. -/
theorem theorem4_stein_lyapunov (c : ℝ) (hc : 0 ≤ c) (ΔT : ℝ)
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty E]
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w))
    (hΔT : 0 < ΔT) (hstep : ΔT < deltaTStar) :
    let H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
      (Bᵀ.mulVec (onShellPotential B eta w))
    let A := leapfrogLin 3 ΔT H
    Aᵀ * steinP A * A - steinP A = -1 ∧
      (steinP A).PosDef ∧
        ∀ x, x ⬝ᵥ x ≤ (steinP A).mulVec x ⬝ᵥ x := by
  intro H A
  have hρ := theorem4_spectralRadius_lt_one c hc ΔT B eta w hbal hconn hadm hF hΔT hstep
  simpa [A] using stein_lyapunov_exists (A := A) hρ

end UniversalStability
