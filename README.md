# Convergence of the normalized state vector in the positive linear system ẋ = Mx

A Lean 4 formalization, on top of Mathlib, of the following theorem.

> Let `M` be a real square matrix with nonnegative off-diagonal entries (a Metzler matrix), and
> let `x(t)` solve `ẋ = Mx` from a nonnegative, nonzero initial state. Then the normalized
> solution `x(t) / Σᵢ xᵢ(t)` converges to a nonnegative eigenvector of `M`. No irreducibility is
> assumed.

The precise statement, with the eigenvalue identified, is Theorem 2 of the accompanying text,
`Positive linear system convergence.tex`. The text gives the proof in ordinary mathematical
language; its Section 4 explains how to read the formal statement and where the formal proof
differs from the text.

## Where things are

The main theorem is `PosLinearSys.tendsto_normalized_solution`, in
`PosLinearSysConvergence/Main.lean`.

| File | Content |
|---|---|
| `PosLinearSysConvergence/Defs.lean` | Metzler matrices; Definition 1 (reachability, the set `R`, the matrix `B`) |
| `PosLinearSysConvergence/MatrixExp.lean` | Lemma 3 (the matrix exponential) |
| `PosLinearSysConvergence/Positivity.lean` | Step 1 (`e^{Mt} ≥ 0`; which entries are positive) |
| `PosLinearSysConvergence/Modes.lean` | Lemma 4 (entries of `e^{At}`); Step 3 |
| `PosLinearSysConvergence/PerronFrobenius.lean` | Lemma 5 (Perron–Frobenius for Metzler matrices) |
| `PosLinearSysConvergence/Main.lean` | Steps 2, 4, 5 and 6; Theorem 2 |

## Building and checking

The project uses Lean 4.36.0 and Mathlib v4.36.0; the versions are fixed by `lean-toolchain` and
`lake-manifest.json`. With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get    # download the compiled Mathlib (several gigabytes)
lake build            # compile and check this project
```

The build succeeds without `sorry`. To see which axioms the main theorem depends on, put

```lean
import PosLinearSysConvergence
#print axioms PosLinearSys.tendsto_normalized_solution
```

in a file `Check.lean` and run `lake env lean Check.lean`. The answer is `propext`,
`Classical.choice` and `Quot.sound`, the standard axioms of classical mathematics in Lean.

## License

Copyright 2026 Thomas M. English. Released under the Apache License, Version 2.0; see `LICENSE`.
