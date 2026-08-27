import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Increment (iii) — Stein uniqueness from vanishing powers,
and existence of the Stein series when `ρ < 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UniversalStability

open Matrix Filter Topology

open scoped Matrix.Norms.L2Operator ENNReal NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem stein_iterate (J X : Matrix n n ℝ) (hX : Jᵀ * X * J = X) :
    ∀ k, (Jᵀ) ^ k * X * J ^ k = X := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (Jᵀ), pow_succ]
    have : Jᵀ * (Jᵀ ^ k * X * J ^ k) * J = Jᵀ * X * J := by
      rw [ih]
    simp only [Matrix.mul_assoc] at this ⊢
    rw [this]
    rw [← Matrix.mul_assoc, hX]

theorem stein_unique_of_pow_tendsto (J P Q : Matrix n n ℝ)
    (hP : Jᵀ * P * J - P = -1) (hQ : Jᵀ * Q * J - Q = -1)
    (hpow : Tendsto (fun k : ℕ => (Jᵀ) ^ k * (P - Q) * J ^ k) atTop (nhds 0)) :
    P = Q := by
  have hdiff :
      Jᵀ * (P - Q) * J - (P - Q) =
        (Jᵀ * P * J - P) - (Jᵀ * Q * J - Q) := by
    simp [mul_sub, sub_mul]
    abel
  have hX : Jᵀ * (P - Q) * J = P - Q := by
    have : Jᵀ * (P - Q) * J - (P - Q) = 0 := by
      rw [hdiff, hP, hQ]
      simp
    exact sub_eq_zero.mp this
  have hiter := stein_iterate J (P - Q) hX
  have hlim0 : Tendsto (fun _ : ℕ => P - Q) atTop (nhds 0) := by
    convert hpow using 1
    funext k
    exact (hiter k).symm
  have : (0 : Matrix n n ℝ) = P - Q :=
    tendsto_nhds_unique hlim0 tendsto_const_nhds
  exact eq_of_sub_eq_zero this.symm

/-- Complexification of a real matrix. -/
def ofRealMat {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofRealHom

theorem ofRealMat_mul {l m n : Type*} [Fintype m]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    ofRealMat (A * B) = ofRealMat A * ofRealMat B :=
  Matrix.map_mul

theorem ofRealMat_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (k : ℕ) :
    ofRealMat (A ^ k) = ofRealMat A ^ k :=
  map_pow Complex.ofRealHom.mapMatrix A k

theorem ofRealMat_one {ι : Type*} [DecidableEq ι] :
    ofRealMat (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)

theorem ofRealMat_transpose {m n : Type*} (A : Matrix m n ℝ) :
    ofRealMat Aᵀ = (ofRealMat A)ᵀ := by
  ext i j
  simp [ofRealMat]

theorem ofRealMat_smul {m n : Type*} (c : ℝ) (A : Matrix m n ℝ) :
    ofRealMat (c • A) = (c : ℂ) • ofRealMat A := by
  ext i j
  simp [ofRealMat]

theorem ofRealMat_sub {m n : Type*} (A B : Matrix m n ℝ) :
    ofRealMat (A - B) = ofRealMat A - ofRealMat B := by
  ext i j
  simp [ofRealMat]

theorem ofRealMat_mulVec (A : Matrix n n ℝ) (x : n → ℝ) :
    (ofRealMat A).mulVec (fun i => (x i : ℂ)) = fun i => (A.mulVec x i : ℂ) := by
  ext i
  simp [ofRealMat, mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_mul, map_sum]

/-- Gelfand decay: `ρ(A) < r` yields `‖A^k‖ ≤ C r^k`. -/
theorem exists_gelfand_pow_bound (A : Matrix n n ℂ) {r : ℝ} (hr0 : 0 < r)
    (hρ : spectralRadius ℂ A < ENNReal.ofReal r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * r ^ k := by
  have hlim :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A
  have hev := hlim.eventually (Iio_mem_nhds hρ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let N1 := max N 1
  have hN1 : 1 ≤ N1 := le_max_right _ _
  have htail : ∀ k, N1 ≤ k → ‖A ^ k‖ < r ^ k := by
    intro k hk
    have hkN : N ≤ k := le_trans (le_max_left N 1) hk
    have hk1 : 1 ≤ k := le_trans hN1 hk
    have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk1
    have hlt := (ENNReal.ofReal_lt_ofReal_iff hr0).mp (hN k hkN)
    have hnn : 0 ≤ ‖A ^ k‖ ^ (1 / (k : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hpow : ‖A ^ k‖ = (‖A ^ k‖ ^ (1 / (k : ℝ))) ^ k := by
      have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hkR,
        Real.rpow_one]
    rw [hpow]
    have hrpow :
        (‖A ^ k‖ ^ (1 / (k : ℝ))) ^ (k : ℝ) < r ^ (k : ℝ) :=
      Real.rpow_lt_rpow hnn hlt (Nat.cast_pos.mpr hk1)
    simpa [Real.rpow_natCast] using hrpow
  let C := 1 + ∑ k ∈ Finset.range N1, ‖A ^ k‖ / r ^ k
  have hC0 : 0 ≤ C :=
    add_nonneg zero_le_one
      (Finset.sum_nonneg fun _ _ =>
        div_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hr0) _))
  refine ⟨C, hC0, fun k => ?_⟩
  by_cases hk : k < N1
  · have hkmem : k ∈ Finset.range N1 := Finset.mem_range.mpr hk
    have hrk : 0 < r ^ k := pow_pos hr0 _
    have hterm : ‖A ^ k‖ / r ^ k ≤ ∑ i ∈ Finset.range N1, ‖A ^ i‖ / r ^ i :=
      Finset.single_le_sum (s := Finset.range N1) (f := fun i => ‖A ^ i‖ / r ^ i)
        (fun _ _ => div_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hr0) _)) hkmem
    have : ‖A ^ k‖ / r ^ k ≤ C := le_trans hterm (le_add_of_nonneg_left zero_le_one)
    exact (div_le_iff₀ hrk).mp this
  · have hk' : N1 ≤ k := le_of_not_gt hk
    have : ‖A ^ k‖ ≤ r ^ k := le_of_lt (htail k hk')
    have hC1 : (1 : ℝ) ≤ C := le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ =>
        div_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hr0) _))
    calc
      ‖A ^ k‖ ≤ 1 * r ^ k := by simpa using this
      _ ≤ C * r ^ k := mul_le_mul_of_nonneg_right hC1 (pow_nonneg (le_of_lt hr0) _)

lemma complex_norm_ofReal_sq (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Real L2 operator norm is at most that of the complexification. -/
theorem real_l2_opNorm_le_complex (A : Matrix n n ℝ) :
    ‖A‖ ≤ ‖ofRealMat A‖ := by
  rw [← l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A,
    ← l2_opNorm_toEuclideanCLM (𝕜 := ℂ) (ofRealMat A)]
  refine (toEuclideanCLM (n := n) (𝕜 := ℝ) A).opNorm_le_bound
      (norm_nonneg _) fun x => ?_
  let xc : EuclideanSpace ℂ n := WithLp.toLp 2 fun i => ((WithLp.ofLp x) i : ℂ)
  have hnormx : ‖xc‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
    simpa [xc] using complex_norm_ofReal_sq (WithLp.ofLp x i)
  have hTx : toEuclideanCLM (𝕜 := ℝ) A x =
      WithLp.toLp 2 (A.mulVec (WithLp.ofLp x)) := by
    simpa using toEuclideanCLM_toLp (𝕜 := ℝ) A (WithLp.ofLp x)
  have hTc : toEuclideanCLM (𝕜 := ℂ) (ofRealMat A) xc =
      WithLp.toLp 2 ((ofRealMat A).mulVec fun i => ((WithLp.ofLp x) i : ℂ)) :=
    toEuclideanCLM_toLp _ _
  have hvec := ofRealMat_mulVec A (WithLp.ofLp x)
  have hnormT :
      ‖toEuclideanCLM (𝕜 := ℝ) A x‖ =
        ‖toEuclideanCLM (𝕜 := ℂ) (ofRealMat A) xc‖ := by
    rw [hTx, hTc, hvec]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
    simpa using complex_norm_ofReal_sq (A.mulVec (WithLp.ofLp x) i)
  rw [hnormT, ← hnormx]
  exact (toEuclideanCLM (𝕜 := ℂ) (ofRealMat A)).le_opNorm xc

theorem stein_term_opNorm_le (A : Matrix n n ℝ) (k : ℕ) :
    ‖(Aᵀ) ^ k * A ^ k‖ ≤ ‖A ^ k‖ ^ 2 := by
  have h := l2_opNorm_conjTranspose_mul_self (A ^ k)
  have hT : (A ^ k)ᵀ = (Aᵀ) ^ k := transpose_pow A k
  rw [← hT, pow_two]
  exact h.le

def steinQuadLM (x : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := x ⬝ᵥ M.mulVec x
  map_add' A B := by
    simp [add_mulVec, dotProduct_add]
  map_smul' c A := by
    simp [smul_mulVec, smul_dotProduct]

def steinQuadCLM (x : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (steinQuadLM x)

theorem steinQuadCLM_apply (x : n → ℝ) (M : Matrix n n ℝ) :
    steinQuadCLM x M = x ⬝ᵥ M.mulVec x :=
  rfl

theorem stein_quad_pow (A : Matrix n n ℝ) (x : n → ℝ) (k : ℕ) :
    x ⬝ᵥ (((Aᵀ) ^ k * A ^ k).mulVec x) =
      (A ^ k).mulVec x ⬝ᵥ (A ^ k).mulVec x := by
  have hT : (A ^ k)ᵀ = (Aᵀ) ^ k := transpose_pow A k
  rw [← hT, ← mulVec_mulVec, dotProduct_comm, mulVec_transpose, ← dotProduct_mulVec,
    dotProduct_comm]

def mulSandwichLM (A : Matrix n n ℝ) : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ where
  toFun M := Aᵀ * M * A
  map_add' X Y := by
    simp [mul_add, add_mul]
  map_smul' c X := by
    simp [Matrix.mul_smul, Matrix.smul_mul]

def mulSandwichCLM (A : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap (mulSandwichLM A)

theorem mulSandwichCLM_apply (A M : Matrix n n ℝ) :
    mulSandwichCLM A M = Aᵀ * M * A :=
  rfl

theorem mulSandwich_stein_term (A : Matrix n n ℝ) (k : ℕ) :
    mulSandwichCLM A ((Aᵀ) ^ k * A ^ k) = (Aᵀ) ^ (k + 1) * A ^ (k + 1) := by
  rw [mulSandwichCLM_apply, pow_succ' (Aᵀ), pow_succ]
  simp [Matrix.mul_assoc]

theorem stein_series_summable {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    Summable fun k : ℕ => (Aᵀ) ^ k * A ^ k := by
  have hbtwn := (ENNReal.lt_iff_exists_nnreal_btwn).1
      (show spectralRadius ℂ (ofRealMat A) < (1 : ℝ≥0) from hA)
  obtain ⟨r, hrρ, hr1⟩ := hbtwn
  have hr0 : 0 < (r : ℝ) := by
    have : (0 : ℝ≥0∞) ≤ spectralRadius ℂ (ofRealMat A) := bot_le
    have hpos : (0 : ℝ≥0∞) < r := lt_of_le_of_lt this hrρ
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (by
      intro h
      simp [h] at hpos))
  have hrlt : (r : ℝ) < 1 := by
    have : (r : ℝ≥0∞) < 1 := hr1
    exact_mod_cast this
  have hρr : spectralRadius ℂ (ofRealMat A) < ENNReal.ofReal (r : ℝ) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨C, hC0, hC⟩ := exists_gelfand_pow_bound (ofRealMat A) hr0 hρr
  have hr2 : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
  have hr2lt : (r : ℝ) ^ 2 < 1 := by
    nlinarith [hr0, hrlt]
  have hgeo : Summable fun k : ℕ => C ^ 2 * ((r : ℝ) ^ 2) ^ k :=
    Summable.mul_left _ (summable_geometric_of_lt_one hr2 hr2lt)
  refine Summable.of_norm_bounded (g := fun k => C ^ 2 * ((r : ℝ) ^ 2) ^ k) hgeo fun k => ?_
  have hreal : ‖A ^ k‖ ≤ ‖ofRealMat (A ^ k)‖ := real_l2_opNorm_le_complex (A ^ k)
  have hpow : ofRealMat (A ^ k) = ofRealMat A ^ k := ofRealMat_pow A k
  have hAk : ‖A ^ k‖ ≤ C * (r : ℝ) ^ k := by
    calc
      ‖A ^ k‖ ≤ ‖ofRealMat A ^ k‖ := by simpa [hpow] using hreal
      _ ≤ C * (r : ℝ) ^ k := hC k
  have hterm := stein_term_opNorm_le A k
  have : C * (r : ℝ) ^ k ≥ 0 := mul_nonneg hC0 (pow_nonneg (le_of_lt hr0) _)
  calc
    ‖(Aᵀ) ^ k * A ^ k‖ ≤ ‖A ^ k‖ ^ 2 := hterm
    _ ≤ (C * (r : ℝ) ^ k) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) this).mpr hAk
    _ = C ^ 2 * ((r : ℝ) ^ 2) ^ k := by ring

def steinP (A : Matrix n n ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, (Aᵀ) ^ k * A ^ k

theorem steinP_eq_tsum (A : Matrix n n ℝ) :
    steinP A = ∑' k : ℕ, (Aᵀ) ^ k * A ^ k :=
  rfl

/-- Lyapunov identity for the Stein series. -/
theorem steinP_lyapunov {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    Aᵀ * steinP A * A - steinP A = -1 := by
  have hs := stein_series_summable hA
  have hmap := (mulSandwichCLM A).map_tsum hs
  have hshift : ∑' k : ℕ, mulSandwichCLM A ((Aᵀ) ^ k * A ^ k) =
      ∑' k : ℕ, (Aᵀ) ^ (k + 1) * A ^ (k + 1) := by
    refine tsum_congr fun k => mulSandwich_stein_term A k
  have htail : ∑' k : ℕ, (Aᵀ) ^ (k + 1) * A ^ (k + 1) =
      ∑' k : ℕ, (Aᵀ) ^ k * A ^ k - (Aᵀ) ^ 0 * A ^ 0 := by
    have hzw := hs.tsum_eq_zero_add
    rw [hzw]
    abel
  have h0 : (Aᵀ) ^ 0 * A ^ 0 = (1 : Matrix n n ℝ) := by simp
  have : Aᵀ * steinP A * A = steinP A - 1 := by
    calc
      Aᵀ * steinP A * A = mulSandwichCLM A (steinP A) := (mulSandwichCLM_apply A _).symm
      _ = mulSandwichCLM A (∑' k : ℕ, (Aᵀ) ^ k * A ^ k) := rfl
      _ = ∑' k : ℕ, mulSandwichCLM A ((Aᵀ) ^ k * A ^ k) := hmap
      _ = ∑' k : ℕ, (Aᵀ) ^ (k + 1) * A ^ (k + 1) := hshift
      _ = ∑' k : ℕ, (Aᵀ) ^ k * A ^ k - (Aᵀ) ^ 0 * A ^ 0 := htail
      _ = steinP A - 1 := by rw [h0]; rfl
  rw [this]
  abel

theorem steinP_quad_floor {A : Matrix n n ℝ} (x : n → ℝ)
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    x ⬝ᵥ x ≤ x ⬝ᵥ (steinP A).mulVec x := by
  have hs := stein_series_summable hA
  have hsum :
      x ⬝ᵥ (steinP A).mulVec x =
        ∑' k : ℕ, (A ^ k).mulVec x ⬝ᵥ (A ^ k).mulVec x := by
    rw [← steinQuadCLM_apply, steinP, ContinuousLinearMap.map_tsum _ hs]
    refine tsum_congr fun k => ?_
    simpa [steinQuadCLM_apply] using stein_quad_pow A x k
  have hφ : Summable fun k : ℕ =>
      (A ^ k).mulVec x ⬝ᵥ (A ^ k).mulVec x := by
    convert hs.mapL (steinQuadCLM x) using 1
    funext k
    exact (stein_quad_pow A x k).symm
  have hnn : ∀ k, 0 ≤ (A ^ k).mulVec x ⬝ᵥ (A ^ k).mulVec x := fun k =>
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rw [hsum, hφ.tsum_eq_zero_add]
  simp only [pow_zero, one_mulVec]
  exact le_add_of_nonneg_right (tsum_nonneg fun k => hnn (k + 1))

theorem stein_term_transpose (A : Matrix n n ℝ) (k : ℕ) :
    ((Aᵀ) ^ k * A ^ k)ᵀ = (Aᵀ) ^ k * A ^ k := by
  rw [transpose_mul, transpose_pow, transpose_pow, transpose_transpose]

theorem steinP_transpose {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    (steinP A)ᵀ = steinP A := by
  have hs := stein_series_summable hA
  rw [steinP, Matrix.transpose_tsum]
  exact tsum_congr fun k => stein_term_transpose A k

theorem steinP_isHermitian {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    (steinP A).IsHermitian := by
  change (steinP A)ᴴ = steinP A
  simpa [conjTranspose] using steinP_transpose hA

theorem steinP_posDef {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    (steinP A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (steinP_isHermitian hA) ?_
  intro x hx
  have hxstar : star x = x := by
    funext i
    simp
  rw [hxstar]
  have hfloor := steinP_quad_floor x hA
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hpos : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne hnn ?_
    intro h0
    apply hx
    ext i
    have hsum0 : ∑ j, x j * x j = 0 := by
      simpa [dotProduct] using h0.symm
    have hxj : ∀ j, x j * x j = 0 := by
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
          fun j _ => mul_self_nonneg (x j)).1 hsum0
      intro j
      exact hzero j (Finset.mem_univ j)
    have : x i * x i = 0 := hxj i
    exact mul_self_eq_zero.mp this
  exact lt_of_lt_of_le hpos hfloor

/-- Existence of a Stein solution with Lyapunov identity, positive-definiteness,
and quadratic floor `xᵀx ≤ xᵀ P x`. -/
theorem stein_lyapunov_exists {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (ofRealMat A) < 1) :
    Aᵀ * steinP A * A - steinP A = -1 ∧
      (steinP A).PosDef ∧
        ∀ x, x ⬝ᵥ x ≤ (steinP A).mulVec x ⬝ᵥ x := by
  refine ⟨steinP_lyapunov hA, steinP_posDef hA, fun x => ?_⟩
  simpa [dotProduct_comm] using steinP_quad_floor x hA

end UniversalStability
