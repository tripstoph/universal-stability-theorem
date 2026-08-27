import Lean
import UniversalStability

/-!
Assertion gate for the default library.

Fails elaboration (nonzero exit) if a kernel LAW depends on `sorryAx`
or on any axiom outside `{propext, Classical.choice, Quot.sound}`.
Run from `lean/` via `lake env lean check_axioms.lean`.
-/

open Lean Elab Command

def assertCleanAxioms (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains declName do
    throwError m!"FAILED: unknown declaration {declName}"
  let axioms ← liftCoreM (collectAxioms declName)
  if axioms.contains ``sorryAx then
    throwError m!"FAILED: {declName} depends on sorryAx"
  let extras := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extras.isEmpty do
    throwError m!"FAILED: {declName} depends on non-standard axioms: {extras.toList}"
  logInfo m!"OK {declName}: {axioms.toList}"

def kernelDecls : Array Name := #[
  ``UniversalStability.onShellForceOnShell_hasFDerivAt_of_connected,
  ``UniversalStability.hessian_quad_ge_floor,
  ``UniversalStability.universal_equilibrium_hessian_posdef,
  ``UniversalStability.exists_minimizer_on_orthant_force_zero,
  ``UniversalStability.theorem2B_unique_on_shell_equilibrium,
  ``UniversalStability.theorem3_jury,
  ``UniversalStability.theorem3_modal_jury,
  ``UniversalStability.theorem3_block_schur,
  ``UniversalStability.theorem4_spectralRadius_lt_one,
  ``UniversalStability.theorem4_stein_lyapunov,
  ``UniversalStability.steinP_quad_floor,
  ``UniversalStability.theorem5_local_invariance,
  ``UniversalStability.twoNode_theorem5
]

run_cmd do
  for n in kernelDecls do
    assertCleanAxioms n
