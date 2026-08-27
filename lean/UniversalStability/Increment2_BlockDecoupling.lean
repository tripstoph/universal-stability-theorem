import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

import UniversalStability.Increment1_HessianSpectrum
import UniversalStability.Theorem3

/-!
# Increment (ii) — conjugation to modal blocks; Schur of `modeBlock`

`𝒮 = diag(Q,Q)` intertwines `leapfrogLin ℋ` with `leapfrogLin (Qᵀ ℋ Q)`.
Jury-stable `2×2` blocks are Schur over `ℂ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Polynomial

variable {E : Type*} [Fintype E] [DecidableEq E]

def leapfrogChangeOfBasis (Q : Matrix E E ℝ) : Matrix (E ⊕ E) (E ⊕ E) ℝ :=
  fromBlocks Q 0 0 Q

theorem leapfrogChangeOfBasis_transpose (Q : Matrix E E ℝ) :
    (leapfrogChangeOfBasis Q)ᵀ = leapfrogChangeOfBasis Qᵀ := by
  simp [leapfrogChangeOfBasis, fromBlocks_transpose]

theorem leapfrogChangeOfBasis_mul (Q R : Matrix E E ℝ) :
    leapfrogChangeOfBasis Q * leapfrogChangeOfBasis R = leapfrogChangeOfBasis (Q * R) := by
  simp [leapfrogChangeOfBasis, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]

theorem leapfrogChangeOfBasis_one :
    leapfrogChangeOfBasis (1 : Matrix E E ℝ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [leapfrogChangeOfBasis, fromBlocks, one_apply]

theorem eigenvectorUnitary_mul_star {A : Matrix E E ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix E E ℝ) *
      star (hA.eigenvectorUnitary : Matrix E E ℝ) = 1 :=
  mem_unitaryGroup_iff.mp (hA.eigenvectorUnitary).2

theorem eigenvectorUnitary_star_mul {A : Matrix E E ℝ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix E E ℝ) *
      (hA.eigenvectorUnitary : Matrix E E ℝ) = 1 :=
  mem_unitaryGroup_iff'.mp (hA.eigenvectorUnitary).2

theorem eigenvectorUnitary_star_eq_transpose {A : Matrix E E ℝ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix E E ℝ) =
      (hA.eigenvectorUnitary : Matrix E E ℝ)ᵀ := by
  simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

theorem leapfrogLin_conj (γ ΔT : ℝ) (H Q : Matrix E E ℝ) (hQ : Qᵀ * Q = 1) :
    (leapfrogChangeOfBasis Q)ᵀ * leapfrogLin γ ΔT H * leapfrogChangeOfBasis Q =
      leapfrogLin γ ΔT (Qᵀ * H * Q) := by
  set D := (1 - γ * ΔT) • (1 : Matrix E E ℝ) - ΔT ^ 2 • H
  have hST : (leapfrogChangeOfBasis Q)ᵀ = fromBlocks Qᵀ 0 0 Qᵀ :=
    leapfrogChangeOfBasis_transpose Q
  have hSJ :
      fromBlocks Qᵀ 0 0 Qᵀ * leapfrogLin γ ΔT H =
        fromBlocks Qᵀ (ΔT • Qᵀ) ((-ΔT) • (Qᵀ * H)) (Qᵀ * D) := by
    rw [leapfrogLin]
    convert fromBlocks_multiply Qᵀ (0 : Matrix E E ℝ) (0 : Matrix E E ℝ) Qᵀ
        (1 : Matrix E E ℝ) (ΔT • (1 : Matrix E E ℝ)) ((-ΔT) • H) D using 1
    simp [zero_mul, mul_zero, add_zero, zero_add, Matrix.mul_smul, mul_one]
  have hSJS :
      fromBlocks Qᵀ (ΔT • Qᵀ) ((-ΔT) • (Qᵀ * H)) (Qᵀ * D) * fromBlocks Q 0 0 Q =
        fromBlocks (Qᵀ * Q) (ΔT • (Qᵀ * Q)) ((-ΔT) • (Qᵀ * H * Q))
          (Qᵀ * D * Q) := by
    convert fromBlocks_multiply Qᵀ (ΔT • Qᵀ) ((-ΔT) • (Qᵀ * H)) (Qᵀ * D)
        Q (0 : Matrix E E ℝ) (0 : Matrix E E ℝ) Q using 1
    simp [mul_zero, zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_assoc]
  have hD :
      Qᵀ * D * Q = (1 - γ * ΔT) • (1 : Matrix E E ℝ) - ΔT ^ 2 • (Qᵀ * H * Q) := by
    simp [D, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hQ, Matrix.mul_assoc]
  rw [hST, hSJ, leapfrogChangeOfBasis, hSJS, hQ, hD, leapfrogLin]

theorem modeBlock_charpoly (γ ΔT eig : ℝ) :
    (modeBlock γ ΔT eig).charpoly =
      X ^ 2 - C (modeBlock γ ΔT eig).trace * X + C (modeBlock γ ΔT eig).det :=
  charpoly_fin_two _

theorem modeBlock_eval_charpoly_map (γ ΔT eig : ℝ) (μ : ℂ) :
    ((modeBlock γ ΔT eig).charpoly.map Complex.ofRealHom).eval μ =
      μ ^ 2 - (modeBlock γ ΔT eig).trace * μ + (modeBlock γ ΔT eig).det := by
  rw [modeBlock_charpoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_X, Polynomial.map_C, Polynomial.map_C, eval_add, eval_sub,
    eval_mul, eval_pow, eval_X, eval_C, eval_C]
  simp [Complex.ofRealHom]

lemma complex_sq_re (μ : ℂ) : (μ ^ 2).re = μ.re ^ 2 - μ.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

lemma complex_sq_im (μ : ℂ) : (μ ^ 2).im = 2 * μ.re * μ.im := by
  simp [pow_two, Complex.mul_im]
  ring

/-- Jury-stable `2×2` blocks are Schur: every complex characteristic root has modulus `< 1`. -/
theorem modeBlock_complex_root_norm_lt_one (γ ΔT eig : ℝ) (μ : ℂ)
    (heig : 0 < eig) (hΔT : ΔT ≠ 0) (hJ : JuryStable γ ΔT eig)
    (hroot : ((modeBlock γ ΔT eig).charpoly.map Complex.ofRealHom).eval μ = 0) :
    ‖μ‖ < 1 := by
  have htd := (juryStable_iff_trace_det γ ΔT eig heig hΔT).mp hJ
  set τ := (modeBlock γ ΔT eig).trace
  set δ := (modeBlock γ ΔT eig).det
  have heq : μ ^ 2 - (τ : ℂ) * μ + (δ : ℂ) = 0 := by
    simpa [modeBlock_eval_charpoly_map, τ, δ] using hroot
  have hδabs : |δ| < 1 := by simpa [δ, modeBlock_det] using htd.1
  have hre0 : (μ ^ 2).re - τ * μ.re + δ = 0 := by
    have := congrArg Complex.re heq
    simpa [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re] using this
  have him0 : (μ ^ 2).im - τ * μ.im = 0 := by
    have := congrArg Complex.im heq
    simpa [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im] using this
  by_cases him : μ.im = 0
  · have hreal : μ.re ^ 2 - τ * μ.re + δ = 0 := by
      have := hre0
      rw [complex_sq_re, him] at this
      linarith
    have habs :=
      juryStable_real_root_abs_lt_one γ ΔT eig μ.re heig hΔT hJ (by simpa [τ, δ] using hreal)
    have hμ : μ = μ.re := Complex.ext (by simp) him
    rwa [hμ, Complex.norm_real]
  · have hreμ : μ.re = τ / 2 := by
      have : 2 * μ.re * μ.im - τ * μ.im = 0 := by
        have := him0
        rw [complex_sq_im] at this
        linarith
      have hfac : μ.im * (2 * μ.re - τ) = 0 := by linarith
      have : 2 * μ.re - τ = 0 := (mul_eq_zero.mp hfac).resolve_left him
      linarith
    have hsumsq : μ.re ^ 2 + μ.im ^ 2 = δ := by
      rw [hreμ]
      have := hre0
      rw [complex_sq_re, hreμ] at this
      linarith
    have hn : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hnormsq : ‖μ‖ ^ 2 = δ := hn.trans hsumsq
    have hsq : ‖μ‖ ^ 2 < 1 := lt_of_eq_of_lt hnormsq (abs_lt.mp hδabs).2
    have hnn : 0 ≤ ‖μ‖ := norm_nonneg μ
    have habs : |‖μ‖| < 1 := (sq_lt_one_iff_abs_lt_one (a := ‖μ‖)).mp hsq
    rwa [abs_of_nonneg hnn] at habs

/-- Orthogonal conjugation: `𝒮ᵀ 𝒥 𝒮 = leapfrogLin(diag λ)`. -/
theorem theorem4_conj_form (c : ℝ) (_hc : 0 ≤ c) (ΔT : ℝ)
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V E ℝ) (eta : V → ℝ) (w : E → ℝ)
    (_hbal : incidenceBalanced B) (_hconn : IncidenceConnected B)
    (_hadm : ∀ e, (1 / 3 : ℝ) ≤ w e)
    (_hF : ForceBalanceC c B w (onShellPotential B eta w)) :
    let H := onShellHessianC c B (shiftedWeightedLap B w)⁻¹ w
      (Bᵀ.mulVec (onShellPotential B eta w))
    let hH := onShellHessianC_shifted_isHermitian c B w
      (Bᵀ.mulVec (onShellPotential B eta w))
    let Q := (hH.eigenvectorUnitary : Matrix E E ℝ)
    (leapfrogChangeOfBasis Q)ᵀ *
        leapfrogLin 3 ΔT H * leapfrogChangeOfBasis Q =
      leapfrogLin 3 ΔT (diagonal hH.eigenvalues) := by
  intro H hH Q
  have hstar : star Q = Qᵀ := eigenvectorUnitary_star_eq_transpose hH
  have hQQ : Qᵀ * Q = 1 := by
    rw [← hstar]
    exact eigenvectorUnitary_star_mul hH
  have hdiag := hessian_conj_is_diagonal c B w
    (Bᵀ.mulVec (onShellPotential B eta w))
  have hconj := leapfrogLin_conj 3 ΔT H Q hQQ
  rw [hdiag] at hconj
  exact hconj

end UniversalStability
