import PosLinearSysConvergence.Defs
import PosLinearSysConvergence.MatrixExp
import PosLinearSysConvergence.Positivity
import PosLinearSysConvergence.Modes
import PosLinearSysConvergence.PerronFrobenius
import PosLinearSysConvergence.Main

/-!
# Convergence of the normalized solution of a positive linear system

Lean formalization of Theorem 2 of the text, `Positive linear system convergence.tex`
("Convergence of type frequencies in the positive linear system `ẋ = M x`"): if `M` is a Metzler
matrix and the initial state is nonnegative and nonzero, then the normalized solution of
`ẋ = M x` converges to a nonnegative eigenvector of `M`.

The main statement is `PosLinearSys.tendsto_normalized_solution`, in
`PosLinearSysConvergence/Main.lean`. The files follow the text:

| File | Content |
|---|---|
| `Defs.lean` | Metzler matrices; Definition 1 (reachability, `R`, `B = M_RR`) |
| `MatrixExp.lean` | Lemma 3 (the matrix exponential) |
| `Positivity.lean` | Step 1 (`e^{Mt} ≥ 0`; reachability decides which entries are positive) |
| `Modes.lean` | Lemma 4 (entries of `e^{At}`); Step 3 (the leading term of `e^{Bt}`) |
| `PerronFrobenius.lean` | Lemma 5 (Perron–Frobenius for Metzler matrices) |
| `Main.lean` | Steps 2, 4, 5, 6 and Theorem 2 |
-/
