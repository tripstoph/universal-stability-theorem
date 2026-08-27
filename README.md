# universal-stability-theorem

Lean 4 / Mathlib 4.28 formalization of the
[Universal Stability Theorem for On-Shell Flow-Adaptive Networks](Universal%20Stability%20Theorem%20for%20On-Shell%20Flow-Adaptive%20Networks.md).

Build the sorry-free kernel from `lean/`:

```bash
cd lean
lake exe cache get
lake build UniversalStability
```

See [`lean/README.md`](lean/README.md) for pins, LAW vs `USIncomplete`, and module layout.
