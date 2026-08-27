#!/usr/bin/env bash
set -eo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/lean"

echo "==> Fetching Mathlib cache..."
lake exe cache get

echo "==> Building UniversalStability library..."
lake build UniversalStability

echo "==> Auditing kernel axioms..."
# Fails (exit 1) on sorryAx or axioms outside {propext, Classical.choice, Quot.sound}.
lake env lean check_axioms.lean

echo "==> SUCCESS: UniversalStability verified with 0 sorries and a standard axiom whitelist."
