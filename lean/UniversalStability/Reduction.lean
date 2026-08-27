import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.Basic

import UniversalStability.Theorem2A

/-!
# Reduction for Theorem 2B (honest name)

Two distinct strict local minima of a `C²` coercive function force a third
critical point that is not a local minimum, *if* a mountain-pass lemma is
supplied. This file does not claim uniqueness of the on-shell equilibrium.
-/

set_option autoImplicit false

noncomputable section

namespace UniversalStability

open Set

variable {E : Type*} [Fintype E]

/-- Finite-dimensional mountain-pass hypothesis: two distinct strict local
minima of `f` on an open set `Ω` produce a third critical point that is not
a local minimizer. -/
def MountainPassOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : Set F) (f : F → ℝ) : Prop :=
  ∀ x y : F, x ∈ Ω → y ∈ Ω → x ≠ y →
    IsLocalMin f x → IsLocalMin f y →
      ∃ z ∈ Ω, z ≠ x ∧ z ≠ y ∧ (∀ dw, fderiv ℝ f z dw = 0) ∧ ¬ IsLocalMin f z

/-- Honest name for the mountain-pass conclusion (not uniqueness). -/
theorem third_crit_point_of_two_strict_local_mins {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : Set F) (f : F → ℝ) (hMP : MountainPassOn Ω f)
    {x y : F} (hx : x ∈ Ω) (hy : y ∈ Ω) (hne : x ≠ y)
    (hxmin : IsLocalMin f x) (hymin : IsLocalMin f y) :
    ∃ z ∈ Ω, z ≠ x ∧ z ≠ y ∧ (∀ dw, fderiv ℝ f z dw = 0) ∧ ¬ IsLocalMin f z :=
  hMP x y hx hy hne hxmin hymin

/-- **Reduction (not uniqueness).** If every critical point is a strict local
minimum and mountain pass holds, there is at most one critical point. -/
theorem at_most_one_crit_of_mountain_pass {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : Set F) (f : F → ℝ) (hMP : MountainPassOn Ω f)
    (hstrict : ∀ z ∈ Ω, (∀ dw, fderiv ℝ f z dw = 0) → IsLocalMin f z)
    {x y : F} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hdx : ∀ dw, fderiv ℝ f x dw = 0) (hdy : ∀ dw, fderiv ℝ f y dw = 0) :
    x = y := by
  by_contra hne
  obtain ⟨z, hz, hzx, hzy, hcrit, hnot⟩ :=
    hMP x y hx hy hne (hstrict x hx hdx) (hstrict y hy hdy)
  exact hnot (hstrict z hz hcrit)

end UniversalStability
