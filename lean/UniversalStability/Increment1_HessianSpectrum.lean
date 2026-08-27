import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

import UniversalStability.Force
import UniversalStability.ShiftedGreen
import UniversalStability.Theorem2
import UniversalStability.Theorem3

/-!
# Increment (i) — symmetry and spectral decomposition of `ℋ`

`M_w` is Hermitian, hence so is `M_w⁻¹` and `K_w = Bᵀ M_w⁻¹ B`.
The algebraic Hessian is therefore Hermitian. Eigenvalues lie in
`[universalFloor, 1464]` at force balance on `{w_e ≥ 1/3}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem transferMatrix_isHermitian (B : Matrix V E ℝ) {Lpinv : Matrix V V ℝ}
    (hL : Lpinv.IsHermitian) :
    (Bᵀ * Lpinv * B).IsHermitian := by
  change (Bᵀ * Lpinv * B)ᴴ = Bᵀ * Lpinv * B
  have hB : (Bᵀ : Matrix E V ℝ)ᴴ = B := by
    simp [conjTranspose_eq_transpose_of_trivial]
  have hBT : (B : Matrix V E ℝ)ᴴ = Bᵀ := by
    simp [conjTranspose_eq_transpose_of_trivial]
  have hL' : Lpinvᴴ = Lpinv := hL.eq
  rw [conjTranspose_mul, conjTranspose_mul, hL', hB, hBT]
  exact (Matrix.mul_assoc Bᵀ Lpinv B).symm

theorem onShellHessianC_isHermitian (c : ℝ) (B : Matrix V E ℝ)
    {Lpinv : Matrix V V ℝ} (hL : Lpinv.IsHermitian) (w dPsi : E → ℝ) :
    (onShellHessianC c B Lpinv w dPsi).IsHermitian := by
  change (onShellHessianC c B Lpinv w dPsi)ᴴ =
    onShellHessianC c B Lpinv w dPsi
  rw [conjTranspose_eq_transpose_of_trivial]
  ext i j
  have hKsym : (Bᵀ * Lpinv * B).IsHermitian := transferMatrix_isHermitian B hL
  have hK : (Bᵀ * Lpinv * B) j i = (Bᵀ * Lpinv * B) i j := by
    have htr : (Bᵀ * Lpinv * B)ᵀ = Bᵀ * Lpinv * B := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hKsym.eq
    calc
      (Bᵀ * Lpinv * B) j i = (Bᵀ * Lpinv * B)ᵀ i j := rfl
      _ = (Bᵀ * Lpinv * B) i j := congr_fun (congr_fun htr i) j
  unfold onShellHessianC
  simp [Matrix.transpose_apply]
  split_ifs with h₁ h₂ h₃
  · simp [h₁]
  · exact (h₂ h₁.symm).elim
  · exact (h₁ h₃.symm).elim
  · rw [hK]
    ring

theorem onShellHessianC_shifted_isHermitian (c : ℝ) (B : Matrix V E ℝ)
    (w dPsi : E → ℝ) :
    (onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w dPsi).IsHermitian :=
  onShellHessianC_isHermitian c B
    (shiftedWeightedLap_isHermitian B w).inv w dPsi

theorem hermitian_eigenvalue_eq_rayleigh {A : Matrix E E ℝ}
    (hA : A.IsHermitian) (i : E) :
    hA.eigenvalues i =
      dotProduct (⇑(hA.eigenvectorBasis i))
        (A.mulVec (⇑(hA.eigenvectorBasis i))) := by
  simpa [RCLike.re_to_real, star_trivial] using hA.eigenvalues_eq i

theorem hermitian_eigenvector_norm_sq {A : Matrix E E ℝ}
    (hA : A.IsHermitian) (i : E) :
    dotProduct (⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i)) = 1 := by
  have hn : ‖hA.eigenvectorBasis i‖ = 1 :=
    hA.eigenvectorBasis.orthonormal.1 i
  have hinner :
      inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hdot := EuclideanSpace.inner_eq_star_dotProduct
    (hA.eigenvectorBasis i) (hA.eigenvectorBasis i)
  have : (hA.eigenvectorBasis i).ofLp ⬝ᵥ star (hA.eigenvectorBasis i).ofLp = 1 := by
    rw [← hdot]
    exact hinner
  simpa [star_trivial] using this

theorem hermitian_eigenvalue_le_of_quad {A : Matrix E E ℝ} (hA : A.IsHermitian)
    {M : ℝ} (hM : ∀ x, dotProduct x (A.mulVec x) ≤ M * dotProduct x x)
    (i : E) : hA.eigenvalues i ≤ M := by
  have hlam := hermitian_eigenvalue_eq_rayleigh hA i
  have hn := hermitian_eigenvector_norm_sq hA i
  have hq := hM (⇑(hA.eigenvectorBasis i))
  calc
    hA.eigenvalues i = (hA.eigenvectorBasis i).ofLp ⬝ᵥ A.mulVec (hA.eigenvectorBasis i).ofLp :=
      hlam
    _ ≤ M * ((hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis i).ofLp) := hq
    _ = M := by rw [hn, mul_one]

theorem hermitian_eigenvalue_ge_of_quad {A : Matrix E E ℝ} (hA : A.IsHermitian)
    {m : ℝ} (hm : ∀ x, m * dotProduct x x ≤ dotProduct x (A.mulVec x))
    (i : E) : m ≤ hA.eigenvalues i := by
  have hlam := hermitian_eigenvalue_eq_rayleigh hA i
  have hn := hermitian_eigenvector_norm_sq hA i
  have hq := hm (⇑(hA.eigenvectorBasis i))
  calc
    m = m * ((hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis i).ofLp) := by
      rw [hn, mul_one]
    _ ≤ (hA.eigenvectorBasis i).ofLp ⬝ᵥ A.mulVec (hA.eigenvectorBasis i).ofLp := hq
    _ = hA.eigenvalues i := hlam.symm

/-- Increment (i): eigenvalues of `ℋ` lie in `[universalFloor, 1464]`. -/
theorem hessian_eigenvalues_mem_interval (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ) [Nonempty V]
    (hbal : incidenceBalanced B) (hconn : IncidenceConnected B)
    (hadm : ∀ e, (1 / 3 : ℝ) ≤ w e)
    (hF : ForceBalanceC c B w (onShellPotential B eta w)) (i : E) :
    universalFloor ≤
        (onShellHessianC_shifted_isHermitian c B w
          (Bᵀ.mulVec (onShellPotential B eta w))).eigenvalues i ∧
      (onShellHessianC_shifted_isHermitian c B w
          (Bᵀ.mulVec (onShellPotential B eta w))).eigenvalues i ≤ 1464 := by
  set H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
    (Bᵀ.mulVec (onShellPotential B eta w))
  set hH := onShellHessianC_shifted_isHermitian c B w
    (Bᵀ.mulVec (onShellPotential B eta w))
  have hRay := theorem3_rayleigh_bounds (E := E) c hc B eta w
  have hdot : ∀ x : E → ℝ, dotProduct x x = ∑ e, x e ^ 2 := by
    intro x
    simp [dotProduct, pow_two]
  constructor
  · refine hermitian_eigenvalue_ge_of_quad hH (fun x => ?_) i
    rw [hdot]
    simpa [H] using (hRay x hbal hconn hadm hF).1
  · refine hermitian_eigenvalue_le_of_quad hH (fun x => ?_) i
    rw [hdot]
    simpa [H] using (hRay x hbal hconn hadm hF).2

/-- Spectral theorem: `ℋ = Q diag(λ) Q⋆`. -/
theorem hessian_spectral_decomposition (c : ℝ) (B : Matrix V E ℝ)
    (w dPsi : E → ℝ) :
    let H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w dPsi
    let hH := onShellHessianC_shifted_isHermitian c B w dPsi
    H =
      (hH.eigenvectorUnitary : Matrix E E ℝ) *
        diagonal hH.eigenvalues *
        star (hH.eigenvectorUnitary : Matrix E E ℝ) := by
  intro H hH
  have hspec := hH.spectral_theorem
  simpa [Unitary.conjStarAlgAut_apply, Function.comp, RCLike.ofReal] using hspec

/-- `Qᵀ ℋ Q = diag(λ)` for the eigenvector unitary `Q`. -/
theorem hessian_conj_is_diagonal (c : ℝ) (B : Matrix V E ℝ)
    (w dPsi : E → ℝ) :
    let H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w dPsi
    let hH := onShellHessianC_shifted_isHermitian c B w dPsi
    let Q := (hH.eigenvectorUnitary : Matrix E E ℝ)
    Qᵀ * H * Q = diagonal hH.eigenvalues := by
  intro H hH Q
  have hstar : star Q = Qᵀ := by
    simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hdiag := hH.conjStarAlgAut_star_eigenvectorUnitary
  have : star Q * H * Q = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    simpa [Unitary.conjStarAlgAut_apply] using hdiag
  simpa [hstar, Function.comp, RCLike.ofReal] using this

end UniversalStability
