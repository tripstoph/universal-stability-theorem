# Lean 4 — Universal Stability (Mathlib v4.28.0)

Formalization of
[Universal Stability Theorem for On-Shell Flow-Adaptive Networks](../Universal%20Stability%20Theorem%20for%20On-Shell%20Flow-Adaptive%20Networks.md).

The method (shifted Green inverse, Thomson energy, zero-`sorry` default
library, incomplete work in a second Lake lib) follows RRT v10. This
repository is standalone: it does not import RRT.

## Pins

- Lean: `leanprover/lean4:v4.28.0` (`lean-toolchain`)
- Mathlib: `v4.28.0` (`lakefile.toml`)

Mathlib 4.28 has no matrix Moore–Penrose `⁺`. The Green map in this
library is the **shifted** inverse `M_w = L_w + J/|V|`.

## Build

From this directory:

```bash
lake exe cache get
lake build UniversalStability
```

`lake build` (default target) is `UniversalStability` and must be
sorry-free.

## LAW vs `USIncomplete`

| Library | Role |
|---|---|
| `UniversalStability` | Kernel. Theorems 1, 2, 2A, 2B, 3, Hessian spectrum, leapfrog conjugation, modal Schur, `ρ(𝒥)<1`, Stein series `𝒫` with `AᵀPA−P=−I` and `P⪰I`, `ContDiffOn ℝ 2 F_c` and quadratic remainder, kinematic bound. **No `sorry`.** Full Theorem 5 (nonlinear ellipsoid containment) remains classical. |
| `USIncomplete` | Finite-dimensional mountain pass and Hessian second-derivative test. **May contain `sorry`.** Not in the default CI target. |

Do not cite mountain pass as the uniqueness proof. The kernel LAW is
`UniversalStability.theorem2B_unique_on_shell_equilibrium`
(constitutive I–V monotonicity from `h(w)>0`).

## Layout

```
UniversalStability.lean          # barrel import
UniversalStability/
  Constitutive.lean              # V, V', V'', h, floor
  Projector.lean                 # 0 ≼ Π ≼ I
  Graph.lean                     # L_w, Thomson
  ShiftedGreen.lean              # M_w invertible on connected B
  TransferLoewner.lean           # Bᵀ M⁻¹ B = W⁻¹ᐟ² Π W⁻¹ᐟ² ≼ W⁻¹
  Force.lean                     # F_c, Φ, Hessian
  Theorem1.lean                  # HasFDerivAt F_c = ℋ
  Theorem2.lean                  # Hessian floor at force balance
  Theorem2A.lean                 # ∇Φ = F_c, coercivity on Ω, compact sublevels, global min
  Theorem2B.lean                 # unique equilibrium via σ'(t) = w h(w)/V''(w) > 0
  Reduction.lean                 # mountain-pass ⇒ at most one crit (unused for 2B)
  Theorem3.lean                  # γ=3 Jury, ΔT★, leapfrogLin, Schur, Lyapunov
  Increment1_HessianSpectrum.lean # ℋ Hermitian, QΛQᵀ, λ ∈ [floor, 1464]
  Increment2_BlockDecoupling.lean # 𝒮ᵀ 𝒥 𝒮 = leapfrogLin(diag λ); modal Schur over ℂ
  Increment3_SteinLyapunov.lean   # Stein series ∑ (Aᵀ)^k A^k, AᵀPA−P=−I, P ⪰ I
  Increment4_NonlinearEllipsoid.lean # ‖δw+ΔT v‖ ≤ √(1+ΔT²) √(‖δw‖²+‖v‖²)
  Increment5_LeapfrogSpectrum.lean # spec(leapfrogLin(diag λ)); ρ(𝒥)<1; Stein Lyapunov
  Increment6_ForceSmooth.lean     # ContDiffOn ℝ 2 F_c on Ω; quadratic Taylor remainder
USIncomplete/
  MountainPass.lean              # finite-dim MP (sorry; not used for uniqueness)
  Theorem2B.lean                 # second-derivative test (sorry)
```
