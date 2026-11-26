import Mathlib

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
        M.mulVec pStar = μ • pStar ∧ pStar ≠ 0 ∧ IsEigenvalue M (μ : ℂ) := by sorry

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
          ((t : ℂ) ^ (j : ℕ) * Complex.exp (lam ℓ * (t : ℂ))) • C ℓ j := by sorry

/-- Lemma 5. The largest eigenvalue real part is itself an eigenvalue of a Metzler
matrix, and every different eigenvalue has strictly smaller real part. -/
theorem lemma_5 {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (hB : Metzler B)
    (μ : ℝ) (hμ : IsMaxRealPart B μ) :
    IsEigenvalue B (μ : ℂ) ∧
      ∀ z : ℂ, IsEigenvalue B z → z ≠ (μ : ℂ) → z.re < μ := by sorry

end
