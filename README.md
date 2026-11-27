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
| `IndependentCheck/Challenge.lean` | Theorem 2, Lemma 4 and Lemma 5 as stated independently, without proofs (see below) |
| `IndependentCheck/Solution.lean` | The same statements, proved from the files above |

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

## Independent check

The results were also stated in Lean independently of this library, and the library proves that
independent version too.

* `IndependentCheck/Challenge.lean` states Theorem 2, Lemma 4 and Lemma 5 of the text, with its
  own definitions and with `sorry` in place of each proof. It was written by ChatGPT-6.2 Astra
  (OpenAI), with reasoning effort set to `max`, working from the text with every mention of the
  formalization removed, while this repository was private. Astra supplied a Lean file that it
  reported to be byte-identical to the file it had compiled, and `Challenge.lean` is
  byte-identical to the file it supplied (SHA-256
  `ae6c53b5ed916bf1e32f95074dd19b4fedc82c8f920d7782d257954bf0b3bcc9`).
* Read against the text clause by clause, the three statements in that file were found to be
  faithful to it.
* `IndependentCheck/Solution.lean` repeats the definitions and statements of the challenge and
  proves the statements from the theorems of `PosLinearSysConvergence`. It also proves that the
  hypotheses of the three statements can be met, so that none of them holds vacuously.

The two files are compared by Comparator, in the form built into Lake (`lake comparator`, Lake
5.0.0, Lean 4.36.0) and configured by `comparator.json`. Comparator compiles the challenge and
the solution inside a sandbox. It checks that each of `theorem_2`, `lemma_4` and `lemma_5` has
the same statement in both files, that the proofs use no axiom other than `propext`,
`Quot.sound` and `Classical.choice`, and that Lean's kernel accepts them. With the option
`--paranoid` it also runs five further proof checkers that come with Lean:
`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche` and `con-ron`.

`lake comparator --paranoid` accepted the solution, under all six checkers, in a
[run on Linux](https://github.com/TMEnglish/PosLinearSysConvergence/actions/runs/45913369836)
at commit `72efe874b5078856a07afd5e933a8e4f28834055`. No Lean file and no build setting has
changed since that commit: the command

```
git diff --stat 72efe87 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json
```

prints nothing. The workflow `.github/workflows/comparator.yml` repeats the run whenever one of
those files changes. GitHub keeps the log of a run only for a limited time, but the run can be
repeated by anyone, on Linux with [bubblewrap](https://github.com/containers/bubblewrap)
installed:

```
lake exe cache get
lake comparator --paranoid
```

(Comparator's sandbox needs Linux; it is not available on macOS.)

## License

Copyright 2026 Thomas M. English. Released under the Apache License, Version 2.0; see `LICENSE`.
