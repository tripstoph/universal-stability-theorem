import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

import UniversalStability.Reduction

/-!
# Finite-dimensional mountain pass

The deformation lemma on a compact convex subset of a finite-dimensional
space is not yet closed. This file must not be imported by the default
library.
-/

set_option autoImplicit false

noncomputable section

namespace USIncomplete

open UniversalStability

/-- Finite-dimensional Ambrosetti–Rabinowitz mountain pass: two distinct
strict local minima of a `C²` coercive function on an open convex set in a
finite-dimensional real vector space produce a third critical point that
is not a local minimizer.

This is the missing deformation argument. It is **not** a uniqueness
theorem, and it is not in the default library. -/
theorem finite_dim_mountain_pass {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (Ω : Set F) (f : F → ℝ)
    (_hΩ : IsOpen Ω) (_hconv : Convex ℝ Ω)
    (_hC2 : ContDiffOn ℝ 2 f Ω)
    (_hcoerc : ∀ M : ℝ, ∃ K : ℝ, ∀ x ∈ Ω, K < ‖x‖ → M < f x) :
    MountainPassOn Ω f := by
  sorry

end USIncomplete
