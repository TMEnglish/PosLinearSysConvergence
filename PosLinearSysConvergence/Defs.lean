import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Definitions

Definitions for the formalization of Theorem 2 of the text, `Positive linear system convergence.tex`
("Convergence of type frequencies in the positive linear system `ẋ = M x`").

* `PosLinearSys.IsMetzler M`: the off-diagonal entries of `M` are nonnegative (standing hypothesis).
* `PosLinearSys.Arc M j i`, `PosLinearSys.Reachable M j i`: Definition 1 (reachability).
* `PosLinearSys.reachSet M x₀`: the reachable set `R` of the initial state `x₀`.
* `PosLinearSys.reducedMatrix M x₀`: the matrix `B = M_RR` of the reduced system.
-/

namespace PosLinearSys

open Matrix

variable {ι : Type*}

/-- A real square matrix is *Metzler* if its off-diagonal entries are nonnegative. -/
def IsMetzler (M : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ M i j

/-- Definition 1: there is an *arc* from `j` to `i` if `i ≠ j` and `M i j > 0`. -/
def Arc (M : Matrix ι ι ℝ) (j i : ι) : Prop :=
  i ≠ j ∧ 0 < M i j

/-- Definition 1: `i` is *reachable from* `j` if `i = j` or there is a chain of arcs leading from
`j` to `i`. This is the reflexive-transitive closure of `Arc M`. -/
def Reachable (M : Matrix ι ι ℝ) (j i : ι) : Prop :=
  Relation.ReflTransGen (Arc M) j i

theorem Reachable.refl (M : Matrix ι ι ℝ) (i : ι) : Reachable M i i :=
  Relation.ReflTransGen.refl

theorem Reachable.tail {M : Matrix ι ι ℝ} {j a b : ι} (h : Reachable M j a) (hab : Arc M a b) :
    Reachable M j b :=
  Relation.ReflTransGen.tail h hab

theorem Reachable.trans {M : Matrix ι ι ℝ} {j a b : ι} (h : Reachable M j a)
    (hab : Reachable M a b) : Reachable M j b :=
  Relation.ReflTransGen.trans h hab

section Fintype

variable [Fintype ι]

open Classical in
/-- Definition 1: the reachable set `R = {i : i is reachable from some j with x₀ j > 0}`.
(The support `S = {j : x₀ j > 0}` of the initial state is not given a name of its own.) -/
noncomputable def reachSet (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => ∃ j, 0 < x₀ j ∧ Reachable M j i

theorem mem_reachSet {M : Matrix ι ι ℝ} {x₀ : ι → ℝ} {i : ι} :
    i ∈ reachSet M x₀ ↔ ∃ j, 0 < x₀ j ∧ Reachable M j i := by
  simp [reachSet]

/-- `S ⊆ R`: the support of the initial state lies in the reachable set. -/
theorem mem_reachSet_of_pos {M : Matrix ι ι ℝ} {x₀ : ι → ℝ} {j : ι} (hj : 0 < x₀ j) :
    j ∈ reachSet M x₀ :=
  mem_reachSet.2 ⟨j, hj, Reachable.refl M j⟩

/-- The reachable set is closed under following arcs. -/
theorem mem_reachSet_of_arc {M : Matrix ι ι ℝ} {x₀ : ι → ℝ} {j i : ι} (hj : j ∈ reachSet M x₀)
    (h : Arc M j i) : i ∈ reachSet M x₀ := by
  obtain ⟨l, hl, hlj⟩ := mem_reachSet.1 hj
  exact mem_reachSet.2 ⟨l, hl, hlj.tail h⟩

/-- Equation (noarc) of Step 2: no arc leaves `R`. If `j ∈ R` and `i ∉ R` then `M i j = 0`. -/
theorem apply_eq_zero_of_mem_of_notMem {M : Matrix ι ι ℝ} (hM : IsMetzler M) {x₀ : ι → ℝ}
    {i j : ι} (hj : j ∈ reachSet M x₀) (hi : i ∉ reachSet M x₀) : M i j = 0 := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  by_contra hne
  have hpos : 0 < M i j := lt_of_le_of_ne (hM i j hij) (Ne.symm hne)
  exact hi (mem_reachSet_of_arc hj ⟨hij, hpos⟩)

/-- Definition 1: the matrix `B = M_RR` of the reduced system, the principal submatrix of `M` on
the reachable set `R`. -/
def reducedMatrix (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) :
    Matrix (reachSet M x₀) (reachSet M x₀) ℝ :=
  M.submatrix (fun i => (i : ι)) (fun i => (i : ι))

@[simp]
theorem reducedMatrix_apply (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) (i j : reachSet M x₀) :
    reducedMatrix M x₀ i j = M i j :=
  rfl

/-- The reduced matrix `B` is Metzler, because its off-diagonal entries are off-diagonal entries
of `M`. -/
theorem IsMetzler.reducedMatrix {M : Matrix ι ι ℝ} (hM : IsMetzler M) (x₀ : ι → ℝ) :
    IsMetzler (reducedMatrix M x₀) := fun i j hij =>
  hM i j fun h => hij (Subtype.ext h)

end Fintype

end PosLinearSys
