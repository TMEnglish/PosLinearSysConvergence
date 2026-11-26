import Mathlib
import PosLinearSysConvergence

/-!
# An independent statement of the results, proved from this library

`IndependentCheck/Challenge.lean` states Theorem 2, Lemma 4 and Lemma 5 of the text, with `sorry`
in place of each proof. It was written by ChatGPT-6.2 Astra (OpenAI), which was given the text
with every mention of the formalization removed and was not shown this library. That file is
byte-identical to the Lean file Astra supplied.

This file repeats the definitions and the three statements of the challenge word for word, and
proves the statements from the theorems of `PosLinearSysConvergence`:

* `theorem_2` from `PosLinearSys.tendsto_normalized_solution`;
* `lemma_4` from `PosLinearSys.exp_smul_eq_sum_modes`;
* `lemma_5` from `PosLinearSys.exists_dominant_eigenvalue`.

Running `lake comparator` at the project root (it reads `comparator.json`) checks that the three
statements here are the same as those of the challenge, that their proofs use no axiom other
than `propext`, `Quot.sound` and `Classical.choice`, and that Lean's kernel accepts them.

The file has four parts:

* the definitions of the challenge (namespace `PositiveLinearSystem`), copied unchanged;
* the namespace `Bridge`, which relates them to the definitions of this library: the two
  reachable sets have the same members (`Bridge.mem_R_iff`), the two reduced matrices are the
  same matrix up to the names of the indices (`Bridge.reducedMatrix_eq_submatrix`), and the two
  notions of "complex eigenvalue of a real matrix" agree (`Bridge.isEigenvalue_iff_mem_spectrum`);
* the three statements of the challenge, with proofs;
* three lemmas showing that the hypotheses of those statements can be met, so that none of them
  holds vacuously.
-/

open scoped BigOperators Classical Topology

noncomputable section

namespace PositiveLinearSystem

variable {ι : Type*}

/-- Section 1. A Metzler matrix has nonnegative off-diagonal entries. -/
def Metzler (M : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ M i j

/-- Section 1. The initial state is nonnegative and nonzero, and the trajectory
solves the Metzler system on the closed half-line, with a right derivative at zero. -/
def StandingHypotheses [Fintype ι] (M : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) : Prop :=
  Metzler M ∧ (∀ i, 0 ≤ x 0 i) ∧ x 0 ≠ 0 ∧
    ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt x (M.mulVec (x t)) (Set.Ici 0) t

/-- Section 1. The total population at time t is the sum of the coordinates. -/
def W [Fintype ι] (x : ℝ → ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, x t i

/-- Section 1. The frequency of each type is its abundance divided by the total. -/
def p [Fintype ι] (x : ℝ → ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => x t i / W x t

/-- Definition 1. An arc from j to i uses row i and column j. -/
def Arc (M : Matrix ι ι ℝ) (j i : ι) : Prop :=
  i ≠ j ∧ 0 < M i j

/-- Definition 1. Reachability allows a path of zero or more arcs from j to i. -/
def Reachable (M : Matrix ι ι ℝ) (j i : ι) : Prop :=
  Relation.ReflTransGen (Arc M) j i

/-- Definition 1. S consists of the strictly positive coordinates of the initial state. -/
def S (x₀ : ι → ℝ) : Set ι :=
  {j | 0 < x₀ j}

/-- Definition 1. R consists of the indices reachable from some member of S. -/
def R (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) : Set ι :=
  {i | ∃ j ∈ S x₀, Reachable M j i}

/-- Definition 1. B is the principal submatrix on R, with the original index labels. -/
def B (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) : Matrix (R M x₀) (R M x₀) ℝ :=
  M.submatrix Subtype.val Subtype.val

/-- Section 1 and Lemma 5. A complex eigenvalue of a real matrix has a nonzero
complex eigenvector for the matrix obtained by embedding its entries in ℂ. -/
def IsEigenvalue [Fintype ι] (M : Matrix ι ι ℝ) (z : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ (M.map Complex.ofReal).mulVec v = z • v

/-- Theorem 2(b) and Lemma 5. μ is the attained maximum of the eigenvalue real parts. -/
def IsMaxRealPart [Fintype ι] (M : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  IsGreatest (Complex.re '' {z : ℂ | IsEigenvalue M z}) μ

end PositiveLinearSystem

open PositiveLinearSystem

/-! ## Bridge between the two sets of definitions -/

namespace Bridge

/-- The two notions of "complex eigenvalue of a real matrix" agree. -/
theorem isEigenvalue_iff_mem_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (z : ℂ) :
    IsEigenvalue A z ↔ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
  constructor
  · rintro ⟨v, hv, h⟩
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hv⟩
    rw [Matrix.toLin'_apply]
    exact h
  · intro h
    obtain ⟨v, hv, h'⟩ := PosLinearSys.exists_eigenvector_of_mem_spectrum _ h
    exact ⟨v, hv, h'⟩

/-- Relabelling the rows and columns of a matrix does not change its eigenvalues. -/
theorem isEigenvalue_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m)
    (A : Matrix m m ℝ) (z : ℂ) :
    IsEigenvalue (A.submatrix e e) z ↔ IsEigenvalue A z := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v ∘ e.symm, fun h0 => hv ?_, ?_⟩
    · funext i
      simpa using congrFun h0 (e i)
    · have h' : ((A.map Complex.ofReal).submatrix e e).mulVec v = z • v := h
      rw [Matrix.submatrix_mulVec_equiv] at h'
      funext i
      simpa using congrFun h' (e.symm i)
  · rintro ⟨w, hw, h⟩
    refine ⟨w ∘ e, fun h0 => hw ?_, ?_⟩
    · funext i
      simpa using congrFun h0 (e.symm i)
    · change ((A.map Complex.ofReal).submatrix e e).mulVec (w ∘ e) = z • (w ∘ e)
      have hcomp : (w ∘ e) ∘ e.symm = w := by
        funext i
        simp
      rw [Matrix.submatrix_mulVec_equiv, hcomp, h]
      rfl

/-- The two definitions of the reachable set have the same members. -/
theorem mem_R_iff {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) (i : ι) :
    i ∈ R M x₀ ↔ i ∈ PosLinearSys.reachSet M x₀ :=
  PosLinearSys.mem_reachSet.symm

/-- The identification of the two index types of the reduced matrix. -/
def reachEquiv {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) :
    ↥(PosLinearSys.reachSet M x₀) ≃ ↥(R M x₀) :=
  Equiv.subtypeEquivRight fun i => (mem_R_iff M x₀ i).symm

/-- The two reduced matrices are the same matrix, up to that identification. -/
theorem reducedMatrix_eq_submatrix {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x₀ : ι → ℝ) :
    PosLinearSys.reducedMatrix M x₀ =
      (B M x₀).submatrix (reachEquiv M x₀) (reachEquiv M x₀) := by
  ext i j
  rfl

/-- The eigenvalues of the reduced matrix are the same in both formalizations. -/
theorem setOf_isEigenvalue_B {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (x₀ : ι → ℝ) [Fintype ↥(R M x₀)] :
    {z : ℂ | IsEigenvalue (B M x₀) z} =
      spectrum ℂ ((PosLinearSys.reducedMatrix M x₀).map (algebraMap ℝ ℂ)) := by
  ext z
  change IsEigenvalue (B M x₀) z ↔ _
  rw [← isEigenvalue_iff_mem_spectrum, reducedMatrix_eq_submatrix, isEigenvalue_submatrix_equiv]

/-- Theorem 2 in the challenge's definitions, without the two abbreviations `r` and `b`. -/
theorem theorem_2_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : ℝ → Fin n → ℝ)
    (h : StandingHypotheses M x) :
    (∀ t : ℝ, 0 < t → ∀ i ∈ R M (x 0), 0 < x t i) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i ∉ R M (x 0), x t i = 0) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < W x t ∧ W x t ≠ 0) ∧
    ∃ μ : ℝ, IsMaxRealPart (B M (x 0)) μ ∧ IsEigenvalue (B M (x 0)) (μ : ℂ) ∧
      ∃ pStar : Fin n → ℝ,
        Filter.Tendsto (p x) Filter.atTop (𝓝 pStar) ∧
        (∀ i, 0 ≤ pStar i) ∧ (∑ i, pStar i) = 1 ∧
        (∀ i ∉ R M (x 0), pStar i = 0) ∧
        M.mulVec pStar = μ • pStar ∧ pStar ≠ 0 ∧ IsEigenvalue M (μ : ℂ) := by
  obtain ⟨hM, hx0, hx0', hx⟩ := h
  obtain ⟨⟨ha1, ha2, ha3⟩, μ, ⟨hgreat, hμB⟩, pStar, hlim, hnonneg, hsum, hzero, heig, hμM⟩ :=
    PosLinearSys.tendsto_normalized_solution M hM x hx0 hx0' hx
  refine ⟨fun t ht i hi => ha1 t ht i ((mem_R_iff M (x 0) i).1 hi),
    fun t ht i hi => ha2 t ht i fun hi' => hi ((mem_R_iff M (x 0) i).2 hi'),
    fun t ht => ⟨ha3 t ht, (ha3 t ht).ne'⟩, μ, ?_, ?_, pStar, ?_, hnonneg, hsum,
    fun i hi => hzero i fun hi' => hi ((mem_R_iff M (x 0) i).2 hi'), heig, ?_, ?_⟩
  · change IsGreatest (Complex.re '' {z : ℂ | IsEigenvalue (B M (x 0)) z}) μ
    rw [setOf_isEigenvalue_B]
    exact hgreat
  · have hmem : (μ : ℂ) ∈ {z : ℂ | IsEigenvalue (B M (x 0)) z} := by
      rw [setOf_isEigenvalue_B]
      exact (PosLinearSys.ofReal_mem_spectrum_map_iff _ μ).2 hμB
    exact hmem
  · have hp : p x = fun t : ℝ => (∑ i, x t i)⁻¹ • x t := by
      funext t i
      simp [p, W, div_eq_inv_mul]
    rw [hp]
    exact hlim
  · intro h0
    rw [h0] at hsum
    simp at hsum
  · exact (isEigenvalue_iff_mem_spectrum M μ).2
      ((PosLinearSys.ofReal_mem_spectrum_map_iff M μ).2 hμM)

end Bridge

/-- Theorem 2(a–c). The support and positive total, the real eigenvalue of B of
maximal real part, and the normalized limit as a nonnegative eigenvector of M. -/
theorem theorem_2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : ℝ → Fin n → ℝ)
    (h : StandingHypotheses M x) :
    let r := R M (x 0)
    let b := B M (x 0)
    (∀ t : ℝ, 0 < t → ∀ i ∈ r, 0 < x t i) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i ∉ r, x t i = 0) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < W x t ∧ W x t ≠ 0) ∧
    ∃ μ : ℝ, IsMaxRealPart b μ ∧ IsEigenvalue b (μ : ℂ) ∧
      ∃ pStar : Fin n → ℝ,
        Filter.Tendsto (p x) Filter.atTop (𝓝 pStar) ∧
        (∀ i, 0 ≤ pStar i) ∧ (∑ i, pStar i) = 1 ∧
        (∀ i ∉ r, pStar i = 0) ∧
        M.mulVec pStar = μ • pStar ∧ pStar ≠ 0 ∧ IsEigenvalue M (μ : ℂ) :=
  Bridge.theorem_2_aux M x h

/-- Lemma 4. Given the distinct eigenvalues of A and their algebraic multiplicities,
there are constant matrices C ℓ j giving the stated expansion for every real t. -/
theorem lemma_4 {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (lam : Fin r → ℂ) (mult : Fin r → ℕ)
    (hDistinct : Function.Injective lam)
    (hEigenvalues : ∀ z : ℂ,
      Module.End.HasEigenvalue A.toLin' z ↔ ∃ ℓ : Fin r, lam ℓ = z)
    (hMultiplicity : ∀ ℓ, Polynomial.rootMultiplicity (lam ℓ) A.charpoly = mult ℓ) :
    ∃ C : (ℓ : Fin r) → Fin (mult ℓ) → Matrix (Fin m) (Fin m) ℂ,
      ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • A) =
        ∑ ℓ : Fin r, ∑ j : Fin (mult ℓ),
          ((t : ℂ) ^ (j : ℕ) * Complex.exp (lam ℓ * (t : ℂ))) • C ℓ j := by
  obtain ⟨C, hC⟩ := PosLinearSys.exp_smul_eq_sum_modes A
  -- the eigenvalues of `A` are exactly the values of `lam`
  have heig : PosLinearSys.eigenvalues A = Finset.univ.image lam := by
    ext z
    rw [PosLinearSys.mem_eigenvalues, ← Matrix.spectrum_toLin',
      ← Module.End.hasEigenvalue_iff_mem_spectrum, hEigenvalues]
    simp
  refine ⟨fun ℓ j => C (lam ℓ) (j : ℕ), fun t => ?_⟩
  refine (hC (t : ℂ)).trans ?_
  rw [heig, Finset.sum_image fun a _ b _ hab => hDistinct hab]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [hMultiplicity ℓ]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => ((t : ℂ) ^ j * Complex.exp (lam ℓ * (t : ℂ))) • C (lam ℓ) j) (mult ℓ)).symm

/-- Lemma 5. The largest eigenvalue real part is itself an eigenvalue of a Metzler
matrix, and every different eigenvalue has strictly smaller real part. -/
theorem lemma_5 {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (hB : Metzler B)
    (μ : ℝ) (hμ : IsMaxRealPart B μ) :
    IsEigenvalue B (μ : ℂ) ∧
      ∀ z : ℂ, IsEigenvalue B z → z ≠ (μ : ℂ) → z.re < μ := by
  have hset : {z : ℂ | IsEigenvalue B z} = spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
    ext z
    exact Bridge.isEigenvalue_iff_mem_spectrum B z
  -- an eigenvector exists, so the matrix has positive size
  obtain ⟨z₀, ⟨v, hv, -⟩, -⟩ := hμ.1
  obtain ⟨a, -⟩ := Function.ne_iff.1 hv
  have : Nonempty ι := ⟨a⟩
  obtain ⟨μ', hμ', hdom⟩ := PosLinearSys.exists_dominant_eigenvalue (B := B) hB
  have hμ2 : IsGreatest (Complex.re '' spectrum ℂ (B.map (algebraMap ℝ ℂ))) μ := by
    rw [← hset]
    exact hμ
  have hμeq : μ' = μ := (PosLinearSys.isGreatest_re_spectrum hμ' hdom).unique hμ2
  subst hμeq
  exact ⟨(Bridge.isEigenvalue_iff_mem_spectrum B _).2 hμ',
    fun z hz hne => hdom z ((Bridge.isEigenvalue_iff_mem_spectrum B z).1 hz) hne⟩

/-! ## The hypotheses can be met

The three statements above are not vacuous: their hypotheses are satisfiable. -/

namespace Bridge

/-- The hypotheses of `theorem_2` can be met: for every Metzler matrix `M` and every nonnegative,
nonzero `x₀`, the function `t ↦ e^{tM} x₀` satisfies the standing hypotheses and starts at
`x₀`. -/
theorem standingHypotheses_exp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Metzler M)
    (x₀ : Fin n → ℝ) (h0 : ∀ i, 0 ≤ x₀ i) (hne : x₀ ≠ 0) :
    StandingHypotheses M (fun t : ℝ => (NormedSpace.exp (t • M)).mulVec x₀) ∧
      (NormedSpace.exp ((0 : ℝ) • M)).mulVec x₀ = x₀ := by
  have hx0 : (NormedSpace.exp ((0 : ℝ) • M)).mulVec x₀ = x₀ := by
    rw [PosLinearSys.exp_zero_smul, Matrix.one_mulVec]
  refine ⟨⟨hM, ?_, ?_, fun t _ => ?_⟩, hx0⟩
  · change ∀ i, 0 ≤ ((NormedSpace.exp ((0 : ℝ) • M)).mulVec x₀) i
    rw [hx0]
    exact h0
  · change (NormedSpace.exp ((0 : ℝ) • M)).mulVec x₀ ≠ 0
    rw [hx0]
    exact hne
  · exact (PosLinearSys.hasDerivAt_exp_smul_mulVec M x₀ t).hasDerivWithinAt

/-- The hypotheses of `lemma_4` can be met: every complex square matrix has a list of its
distinct eigenvalues, with their algebraic multiplicities. -/
theorem exists_eigenvalue_list {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ∃ (r : ℕ) (lam : Fin r → ℂ) (mult : Fin r → ℕ), Function.Injective lam ∧
      (∀ z : ℂ, Module.End.HasEigenvalue A.toLin' z ↔ ∃ ℓ : Fin r, lam ℓ = z) ∧
      ∀ ℓ, Polynomial.rootMultiplicity (lam ℓ) A.charpoly = mult ℓ := by
  refine ⟨(PosLinearSys.eigenvalues A).card,
    fun ℓ => ((PosLinearSys.eigenvalues A).equivFin.symm ℓ : ℂ),
    fun ℓ => Polynomial.rootMultiplicity ((PosLinearSys.eigenvalues A).equivFin.symm ℓ : ℂ)
      A.charpoly, ?_, ?_, fun _ => rfl⟩
  · intro a b hab
    exact (PosLinearSys.eigenvalues A).equivFin.symm.injective (Subtype.ext hab)
  · intro z
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
      ← PosLinearSys.mem_eigenvalues]
    constructor
    · intro hz
      exact ⟨(PosLinearSys.eigenvalues A).equivFin ⟨z, hz⟩, by simp⟩
    · rintro ⟨ℓ, rfl⟩
      exact ((PosLinearSys.eigenvalues A).equivFin.symm ℓ).2

/-- The hypothesis of `lemma_5` can be met: a real square matrix of positive size has a largest
real part among its eigenvalues. -/
theorem exists_isMaxRealPart {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ) :
    ∃ μ : ℝ, IsMaxRealPart A μ := by
  have hne : (spectrum ℂ (A.map (algebraMap ℝ ℂ))).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _
  obtain ⟨z₀, hz₀, hmax⟩ := Set.exists_max_image (spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    Complex.re (Matrix.finite_spectrum _) hne
  refine ⟨z₀.re, ⟨z₀, (isEigenvalue_iff_mem_spectrum A z₀).2 hz₀, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmax z ((isEigenvalue_iff_mem_spectrum A z).1 hz)

end Bridge

end
