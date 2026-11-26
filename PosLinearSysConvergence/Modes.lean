import PosLinearSysConvergence.MatrixExp
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lemma 4 (entries of the matrix exponential) and its consequences

* `exp_smul_eq_sum_modes` is Lemma 4 of the text: for a complex `m × m` matrix `A` there
  are constant matrices `C lam j` with
  `e^{At} = ∑_{lam eigenvalue of A} ∑_{j < m_lam} t^j e^{lam t} C lam j`,
  where `m_lam` is the algebraic multiplicity of `lam`, that is, its multiplicity as a root of the
  characteristic polynomial (`A.charpoly.rootMultiplicity lam`).

  As in the text, the proof uses the generalized eigenspaces `G_lam` of `A`
  (`MemGenEigenspace A lam v` says that `v ∈ G_lam`) and two standard facts, both taken from
  Mathlib:

  * (i) every vector is a sum of vectors of the `G_lam` (`exists_genEigenspace_decomp`);
  * (ii) the dimension of `G_lam` is the algebraic multiplicity `m_lam`; it gives equation
    (nilpotent), `(A - lam I)^{m_lam} v = 0` for `v ∈ G_lam`
    (`MemGenEigenspace.pow_rootMultiplicity_mulVec`).

* `exp_smul_eq_sum_modes_card` is the same expansion with every inner sum running over `j < m`.
  This is the form in which Step 3 uses Lemma 4 (equation (expansion)).

* `tendsto_exp_smul_apply_zero`: if every eigenvalue has negative real part, `e^{At} → 0`.

* `exists_leading_term_real` is equation (L) of Step 3: if `μ` is a real eigenvalue of the real
  matrix `B` and every other eigenvalue has real part `< μ`, then there are `k` and `L ≠ 0` with
  `e^{Bt} / (t^k e^{μ t}) → L`.
-/

namespace PosLinearSys

open Matrix NormedSpace Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Eigenvalues and eigenvectors of matrices -/

/-- The finite set of eigenvalues of a complex square matrix. -/
noncomputable def eigenvalues (A : Matrix n n ℂ) : Finset ℂ :=
  (Matrix.finite_spectrum A).toFinset

@[simp]
theorem mem_eigenvalues {A : Matrix n n ℂ} {lam : ℂ} :
    lam ∈ eigenvalues A ↔ lam ∈ spectrum ℂ A :=
  Set.Finite.mem_toFinset _

/-- An element of the spectrum of a matrix over a field has an eigenvector. -/
theorem exists_eigenvector_of_mem_spectrum {𝕜 : Type*} [Field 𝕜] (A : Matrix n n 𝕜) {lam : 𝕜}
    (h : lam ∈ spectrum 𝕜 A) : ∃ z : n → 𝕜, z ≠ 0 ∧ A *ᵥ z = lam • z := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at h
  obtain ⟨z, hz⟩ := h.exists_hasEigenvector
  refine ⟨z, hz.2, ?_⟩
  have := hz.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

/-- A nonzero vector killed by a power of `A - lam I` shows that `lam` is an eigenvalue of `A`. -/
theorem mem_spectrum_of_pow_mulVec_eq_zero (A : Matrix n n ℂ) {lam : ℂ} {v : n → ℂ} (hv : v ≠ 0)
    {k : ℕ} (h : ((A - lam • (1 : Matrix n n ℂ)) ^ k) *ᵥ v = 0) : lam ∈ spectrum ℂ A := by
  by_contra hlam
  rw [spectrum.mem_iff, not_not] at hlam
  have hu : IsUnit ((A - lam • (1 : Matrix n n ℂ)) ^ k) := by
    have h1 : A - lam • (1 : Matrix n n ℂ) = -(algebraMap ℂ (Matrix n n ℂ) lam - A) := by
      rw [Algebra.algebraMap_eq_smul_one, neg_sub]
    rw [h1]
    exact hlam.neg.pow k
  obtain ⟨W, hW⟩ := hu.exists_left_inv
  apply hv
  rw [← Matrix.one_mulVec v, ← hW, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-! ### Generalized eigenspaces -/

/-- `MemGenEigenspace A lam v`: the vector `v` lies in the generalized eigenspace
`G_lam = {v : (A - lam I)^k v = 0 for some k}` of the matrix `A`. -/
def MemGenEigenspace (A : Matrix n n ℂ) (lam : ℂ) (v : n → ℂ) : Prop :=
  ∃ k : ℕ, ((A - lam • (1 : Matrix n n ℂ)) ^ k) *ᵥ v = 0

theorem toLin'_sub_smul_one (A : Matrix n n ℂ) (lam : ℂ) :
    Matrix.toLin' A - lam • (1 : Module.End ℂ (n → ℂ)) =
      Matrix.toLin' (A - lam • (1 : Matrix n n ℂ)) := by
  rw [map_sub, map_smul, Matrix.toLin'_one]
  rfl

/-- `MemGenEigenspace` in terms of Mathlib's generalized eigenspaces of linear maps. -/
theorem memGenEigenspace_iff {A : Matrix n n ℂ} {lam : ℂ} {v : n → ℂ} :
    MemGenEigenspace A lam v ↔ v ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) lam := by
  simp only [MemGenEigenspace, Module.End.mem_maxGenEigenspace, toLin'_sub_smul_one,
    ← Matrix.toLin'_pow, Matrix.toLin'_apply]

/-- A nonzero vector of `G_lam` shows that `lam` is an eigenvalue of `A`. -/
theorem MemGenEigenspace.mem_spectrum {A : Matrix n n ℂ} {lam : ℂ} {v : n → ℂ}
    (h : MemGenEigenspace A lam v) (hv : v ≠ 0) : lam ∈ spectrum ℂ A := by
  obtain ⟨k, hk⟩ := h
  exact mem_spectrum_of_pow_mulVec_eq_zero A hv hk

/-- Standard fact (i): every vector of `ℂ^m` is a finite sum of vectors `f lam ∈ G_lam`. -/
theorem exists_genEigenspace_decomp (A : Matrix n n ℂ) (v : n → ℂ) :
    ∃ f : ℂ →₀ (n → ℂ),
      (∀ lam, MemGenEigenspace A lam (f lam)) ∧ (f.sum fun _ x => x) = v := by
  have htop := Module.End.iSup_maxGenEigenspace_eq_top (Matrix.toLin' A)
  have hv : v ∈ ⨆ lam : ℂ, Module.End.maxGenEigenspace (Matrix.toLin' A) lam := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hv
  exact ⟨f, fun lam => memGenEigenspace_iff.2 (hf lam), hsum⟩

/-- Equation (nilpotent): `(A - lam I)^{m_lam} v = 0` for `v ∈ G_lam`, where `m_lam` is the
algebraic multiplicity of `lam`. Indeed `A - lam I` is nilpotent on `G_lam`; so its characteristic
polynomial there is `z^d` with `d = dim G_lam`, and its `d`-th power vanishes by the
Cayley–Hamilton theorem; and `d = m_lam` (standard fact (ii)). -/
theorem MemGenEigenspace.pow_rootMultiplicity_mulVec {A : Matrix n n ℂ} {lam : ℂ} {v : n → ℂ}
    (hv : MemGenEigenspace A lam v) :
    ((A - lam • (1 : Matrix n n ℂ)) ^ A.charpoly.rootMultiplicity lam) *ᵥ v = 0 := by
  have hmem : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) lam := memGenEigenspace_iff.1 hv
  -- `N = A - lam I` maps `G_lam` into itself and is nilpotent there
  have hmaps : ∀ x ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) lam,
      (Matrix.toLin' A - algebraMap ℂ (Module.End ℂ (n → ℂ)) lam) x ∈
        Module.End.maxGenEigenspace (Matrix.toLin' A) lam :=
    Module.End.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes (Matrix.toLin' A) lam) lam
  have hnil := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap
    (Matrix.toLin' A) lam hmaps
  -- so, by Cayley–Hamilton, its power `dim G_lam = m_lam` vanishes on `G_lam`
  have hpow := LinearMap.aeval_self_charpoly
    ((Matrix.toLin' A - algebraMap ℂ (Module.End ℂ (n → ℂ)) lam).restrict hmaps)
  rw [hnil.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X,
    LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin',
    Module.End.pow_restrict _ hmaps] at hpow
  have h := congrArg (fun φ : Module.End ℂ (Module.End.maxGenEigenspace (Matrix.toLin' A) lam) =>
    ((φ ⟨v, hmem⟩ : Module.End.maxGenEigenspace (Matrix.toLin' A) lam) : n → ℂ)) hpow
  simp only [LinearMap.coe_restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h
  -- back to matrices
  have hN : Matrix.toLin' A - algebraMap ℂ (Module.End ℂ (n → ℂ)) lam =
      Matrix.toLin' (A - lam • (1 : Matrix n n ℂ)) := by
    rw [Algebra.algebraMap_eq_smul_one, toLin'_sub_smul_one]
  rw [hN, ← Matrix.toLin'_pow, Matrix.toLin'_apply] at h
  exact h

/-- The algebraic multiplicity of an eigenvalue is at most the size of the matrix. -/
theorem rootMultiplicity_charpoly_le_card (A : Matrix n n ℂ) (lam : ℂ) :
    A.charpoly.rootMultiplicity lam ≤ Fintype.card n := by
  have h := Submodule.finrank_le (Module.End.maxGenEigenspace (Matrix.toLin' A) lam)
  rwa [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin',
    Module.finrank_fintype_fun_eq_card] at h

/-! ### Lemma 4 -/

/-- **Lemma 4** (entries of the matrix exponential). For a complex `m × m` matrix `A` there are
constant matrices `C lam j` such that, for all `t`,
`e^{At} = ∑_{lam} ∑_{j < m_lam} t^j e^{lam t} C lam j`. The outer sum is over the eigenvalues
`lam` of `A`, and `m_lam = A.charpoly.rootMultiplicity lam` is the algebraic multiplicity of
`lam`. -/
theorem exp_smul_eq_sum_modes (A : Matrix n n ℂ) :
    ∃ C : ℂ → ℕ → Matrix n n ℂ, ∀ t : ℂ,
      exp (t • A) = ∑ lam ∈ eigenvalues A,
        ∑ j ∈ Finset.range (A.charpoly.rootMultiplicity lam),
          (t ^ j * Complex.exp (lam * t)) • C lam j := by
  -- write each standard basis vector `e_b` as a sum of vectors `f b lam ∈ G_lam`
  choose f hf hsum using fun b : n => exists_genEigenspace_decomp A (Pi.single b (1 : ℂ))
  -- `C lam j` is the matrix whose `b`-th column is `(1 / j!) (A - lam I)^j (f b lam)`
  refine ⟨fun lam j => Matrix.of fun a b =>
    (j.factorial : ℂ)⁻¹ * (((A - lam • (1 : Matrix n n ℂ)) ^ j) *ᵥ f b lam) a, fun t => ?_⟩
  ext a b
  -- the `b`-th column of `e^{At}` is `e^{At} e_b`
  have hcol : (exp (t • A)) a b = (exp (t • A) *ᵥ Pi.single b (1 : ℂ)) a := by
    rw [Matrix.mulVec_single_one]
    rfl
  -- for `v ∈ G_lam`: `e^{At} v = e^{lam t} ∑_{j < m_lam} t^j / j! (A - lam I)^j v`
  have hgen : ∀ lam : ℂ, exp (t • A) *ᵥ f b lam =
      Complex.exp (lam * t) • ∑ j ∈ Finset.range (A.charpoly.rootMultiplicity lam),
        ((j.factorial : ℂ)⁻¹ * t ^ j) • (((A - lam • (1 : Matrix n n ℂ)) ^ j) *ᵥ f b lam) := by
    intro lam
    rw [exp_smul_eq_cexp_smul A lam t, Matrix.smul_mulVec,
      exp_smul_mulVec_of_pow_mulVec_eq_zero _ _ _ (hf b lam).pow_rootMultiplicity_mulVec t]
  -- only eigenvalues contribute
  have hsub : (f b).support ⊆ eigenvalues A := by
    intro lam hlam
    exact mem_eigenvalues.2 ((hf b lam).mem_spectrum (Finsupp.mem_support_iff.1 hlam))
  have hdecomp : exp (t • A) *ᵥ Pi.single b (1 : ℂ) =
      ∑ lam ∈ eigenvalues A, exp (t • A) *ᵥ f b lam := by
    conv_lhs => rw [← hsum b]
    rw [Finsupp.sum, Matrix.mulVec_sum]
    refine Finset.sum_subset hsub fun lam _ hlam => ?_
    rw [Finsupp.notMem_support_iff.1 hlam, Matrix.mulVec_zero]
  rw [hcol, hdecomp]
  simp only [hgen, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lemma 4 with every inner sum running over `j < m`, the size of the matrix (the coefficients
with `j ≥ m_lam` being zero). This is the form of equation (expansion) in Step 3. -/
theorem exp_smul_eq_sum_modes_card (A : Matrix n n ℂ) :
    ∃ C : ℂ → ℕ → Matrix n n ℂ, ∀ t : ℂ,
      exp (t • A) = ∑ lam ∈ eigenvalues A, ∑ j ∈ Finset.range (Fintype.card n),
        (t ^ j * Complex.exp (lam * t)) • C lam j := by
  obtain ⟨C, hC⟩ := exp_smul_eq_sum_modes A
  refine ⟨fun lam j => if j < A.charpoly.rootMultiplicity lam then C lam j else 0, fun t => ?_⟩
  rw [hC t]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_subset (Finset.range_mono (rootMultiplicity_charpoly_le_card A lam))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range.1 hj, ↓reduceIte]
  · intro j _ hj
    have hj' : ¬ j < A.charpoly.rootMultiplicity lam := fun h => hj (Finset.mem_range.2 h)
    simp only [hj', ↓reduceIte, smul_zero]

/-! ### Asymptotics of the modes -/

/-- Exponential decay beats any power of `t`: `t^j e^{lam t} → 0` if `Re lam < 0`. -/
theorem tendsto_pow_mul_cexp_atTop_zero (j : ℕ) {lam : ℂ} (hlam : lam.re < 0) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ j * Complex.exp (lam * t)) atTop (𝓝 0) := by
  have hδ : 0 < -lam.re := neg_pos.2 hlam
  have h1 : Tendsto (fun t : ℝ => (-lam.re * t) ^ j * Real.exp (-(-lam.re * t))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp (tendsto_id.const_mul_atTop hδ)
  have h2 : Tendsto (fun t : ℝ => ((-lam.re) ^ j)⁻¹ *
      ((-lam.re * t) ^ j * Real.exp (-(-lam.re * t)))) atTop (𝓝 0) := by
    simpa using h1.const_mul (((-lam.re) ^ j)⁻¹)
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hre : (lam * (t : ℂ)).re = -(-lam.re * t) := by simp
  have hne : (-lam.re) ^ j ≠ 0 := (pow_pos hδ j).ne'
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp, hre,
    mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The leading term of an exponential polynomial. Suppose `μ ∈ Λ` is real and every other
`lam ∈ Λ` has `Re lam < μ`; and suppose the coefficients `c μ j` vanish for `k < j < N`. Then
`(∑_{lam ∈ Λ} ∑_{j < N} t^j e^{lam t} c lam j) / (t^k e^{μ t}) → c μ k`. -/
theorem tendsto_sum_modes_div (Λ : Finset ℂ) (N : ℕ) (c : ℂ → ℕ → ℂ) (μ : ℝ) (k : ℕ)
    (hΛ : ∀ lam ∈ Λ, lam ≠ (μ : ℂ) → lam.re < μ) (hμ : (μ : ℂ) ∈ Λ) (hk : k < N)
    (hc : ∀ j, k < j → j < N → c μ j = 0) :
    Tendsto (fun t : ℝ =>
        (∑ lam ∈ Λ, ∑ j ∈ Finset.range N, ((t : ℂ) ^ j * Complex.exp (lam * t)) * c lam j) /
          ((t : ℂ) ^ k * Complex.exp (μ * t))) atTop (𝓝 (c μ k)) := by
  have hinv : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using h
  -- the limit of each term
  have hterm : ∀ lam ∈ Λ, ∀ j ∈ Finset.range N,
      Tendsto (fun t : ℝ => ((t : ℂ) ^ j * Complex.exp (lam * t)) * c lam j /
          ((t : ℂ) ^ k * Complex.exp (μ * t)))
        atTop (𝓝 (if lam = (μ : ℂ) ∧ j = k then c μ k else 0)) := by
    intro lam hlam j hj
    have hjN : j < N := Finset.mem_range.1 hj
    by_cases hlμ : lam = (μ : ℂ)
    · -- the terms `t^j e^{μ t}`
      subst hlμ
      by_cases hjk : j ≤ k
      · have hlim : Tendsto (fun t : ℝ => c μ j * ((t : ℂ))⁻¹ ^ (k - j)) atTop
            (𝓝 (c μ j * (0 : ℂ) ^ (k - j))) := (hinv.pow (k - j)).const_mul (c μ j)
        have hval : c μ j * (0 : ℂ) ^ (k - j) =
            if ((μ : ℂ) = (μ : ℂ) ∧ j = k) then c μ k else 0 := by
          by_cases hjk' : j = k
          · subst hjk'
            simp
          · have : k - j ≠ 0 := by omega
            simp [hjk', this]
        rw [← hval]
        refine hlim.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
        have he : Complex.exp ((μ : ℂ) * t) ≠ 0 := Complex.exp_ne_zero _
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
        rw [Nat.add_sub_cancel_left, pow_add, inv_pow]
        field_simp
      · have hjk' : k < j := not_le.1 hjk
        have hfun : (fun t : ℝ => ((t : ℂ) ^ j * Complex.exp ((μ : ℂ) * t)) * c μ j /
            ((t : ℂ) ^ k * Complex.exp (μ * t))) = fun _ => 0 := by
          funext t
          rw [hc j hjk' hjN, mul_zero, zero_div]
        have hif : (if ((μ : ℂ) = (μ : ℂ) ∧ j = k) then c μ k else 0) = 0 := by
          simp [hjk'.ne']
        rw [hfun, hif]
        exact tendsto_const_nhds
    · -- the terms `t^j e^{lam t}` with `Re lam < μ`
      have hre : (lam - (μ : ℂ)).re < 0 := by
        simpa using sub_neg.2 (hΛ lam hlam hlμ)
      have hdecay := tendsto_pow_mul_cexp_atTop_zero j hre
      have hlim : Tendsto (fun t : ℝ => c lam j *
          ((t : ℂ) ^ j * Complex.exp ((lam - (μ : ℂ)) * t)) * ((t : ℂ))⁻¹ ^ k) atTop
          (𝓝 (c lam j * 0 * (0 : ℂ) ^ k)) := (hdecay.const_mul (c lam j)).mul (hinv.pow k)
      have hif : (if (lam = (μ : ℂ) ∧ j = k) then c μ k else 0) = 0 := by
        simp [hlμ]
      rw [hif]
      have hzero : c lam j * 0 * (0 : ℂ) ^ k = 0 := by ring
      rw [hzero] at hlim
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
      have he : Complex.exp ((μ : ℂ) * t) ≠ 0 := Complex.exp_ne_zero _
      rw [sub_mul, Complex.exp_sub, inv_pow]
      field_simp
  have hlim := tendsto_finsetSum Λ fun lam hlam =>
    tendsto_finsetSum (Finset.range N) fun j hj => hterm lam hlam j hj
  have hval : (∑ lam ∈ Λ, ∑ j ∈ Finset.range N,
      if lam = (μ : ℂ) ∧ j = k then c μ k else 0) = c μ k := by
    rw [Finset.sum_eq_single (μ : ℂ)]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp [hjk]
      · intro hk'
        exact absurd (Finset.mem_range.2 hk) hk'
    · intro lam _ hlam
      simp [hlam]
    · intro h
      exact absurd hμ h
  rw [hval] at hlim
  refine hlim.congr fun t => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Finset.sum_div]

/-! ### Consequences for the matrix exponential -/

/-- Entries of `e^{At}` as exponential polynomials (Lemma 4, entry by entry). -/
theorem exp_smul_apply_eq_sum_modes {A : Matrix n n ℂ} {C : ℂ → ℕ → Matrix n n ℂ}
    (hC : ∀ t : ℂ, exp (t • A) = ∑ lam ∈ eigenvalues A, ∑ j ∈ Finset.range (Fintype.card n),
      (t ^ j * Complex.exp (lam * t)) • C lam j) (t : ℂ) (a b : n) :
    (exp (t • A)) a b = ∑ lam ∈ eigenvalues A, ∑ j ∈ Finset.range (Fintype.card n),
      (t ^ j * Complex.exp (lam * t)) * C lam j a b := by
  rw [hC t]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- If every eigenvalue of the complex matrix `A` has negative real part, then `e^{At} → 0`. -/
theorem tendsto_cexp_smul_apply_zero (A : Matrix n n ℂ) (hA : ∀ lam ∈ spectrum ℂ A, lam.re < 0)
    (a b : n) : Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)) a b) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exp_smul_eq_sum_modes_card A
  have h := tendsto_finsetSum (eigenvalues A) fun lam hlam =>
    tendsto_finsetSum (Finset.range (Fintype.card n)) fun j _ =>
      (tendsto_pow_mul_cexp_atTop_zero j (hA lam (mem_eigenvalues.1 hlam))).mul_const
        (C lam j a b)
  simp only [zero_mul, Finset.sum_const_zero] at h
  refine h.congr fun t => ?_
  rw [exp_smul_apply_eq_sum_modes hC]

/-- If every (complex) eigenvalue of the real matrix `B` has negative real part, then
`e^{Bt} → 0`. -/
theorem tendsto_exp_smul_apply_zero (B : Matrix n n ℝ)
    (hB : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam.re < 0) (a b : n) :
    Tendsto (fun t : ℝ => (exp (t • B)) a b) atTop (𝓝 0) := by
  have h := tendsto_cexp_smul_apply_zero (B.map (algebraMap ℝ ℂ)) hB a b
  have h2 := (Complex.continuous_re.tendsto 0).comp h
  refine h2.congr fun t => ?_
  rw [Function.comp_apply, ← ofReal_exp_smul_apply, Complex.ofReal_re]

/-- Step 3 for a complex matrix: if `μ` is a real eigenvalue of `A` and every other eigenvalue has
real part `< μ`, then `e^{At} / (t^k e^{μ t})` converges to a nonzero matrix `L`, for a suitable
`k`. Here `k` is the largest `j` with `C μ j ≠ 0`, and `L = C μ k`. -/
theorem exists_leading_term (A : Matrix n n ℂ) (μ : ℝ) (hμ : (μ : ℂ) ∈ spectrum ℂ A)
    (hdom : ∀ lam ∈ spectrum ℂ A, lam ≠ (μ : ℂ) → lam.re < μ) :
    ∃ (k : ℕ) (L : Matrix n n ℂ), L ≠ 0 ∧ ∀ a b,
      Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)) a b / ((t : ℂ) ^ k * Complex.exp (μ * t)))
        atTop (𝓝 (L a b)) := by
  classical
  obtain ⟨C, hC⟩ := exp_smul_eq_sum_modes_card A
  have hΛ : ∀ lam ∈ eigenvalues A, lam ≠ (μ : ℂ) → lam.re < μ := fun lam hlam =>
    hdom lam (mem_eigenvalues.1 hlam)
  have hμΛ : (μ : ℂ) ∈ eigenvalues A := mem_eigenvalues.2 hμ
  -- the limit of `e^{At} / (t^k e^{μ t})`, whenever the higher coefficients vanish
  have key : ∀ k, k < Fintype.card n → (∀ j, k < j → j < Fintype.card n → C μ j = 0) →
      ∀ a b, Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)) a b /
        ((t : ℂ) ^ k * Complex.exp (μ * t))) atTop (𝓝 (C μ k a b)) := by
    intro k hk hCk a b
    have h := tendsto_sum_modes_div (eigenvalues A) (Fintype.card n) (fun lam j => C lam j a b)
      μ k hΛ hμΛ hk (fun j hj hjN => by rw [hCk j hj hjN]; rfl)
    refine h.congr fun t => ?_
    rw [exp_smul_apply_eq_sum_modes hC]
  -- some coefficient `C μ j` is nonzero
  have hex : ∃ j, j < Fintype.card n ∧ C μ j ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    obtain ⟨z, hz0, hz⟩ := exists_eigenvector_of_mem_spectrum A hμ
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hz0
    have hpos : 0 < Fintype.card n := Fintype.card_pos_iff.2 ⟨a⟩
    have hlim : ∀ b, Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)) a b /
        ((t : ℂ) ^ 0 * Complex.exp (μ * t))) atTop (𝓝 0) := by
      intro b
      have h := key 0 hpos (fun j _ hjN => hall j hjN) a b
      rwa [hall 0 hpos] at h
    have hsum := tendsto_finsetSum Finset.univ fun b (_ : b ∈ Finset.univ) =>
      (hlim b).mul_const (z b)
    simp only [zero_mul, Finset.sum_const_zero] at hsum
    have hconst : ∀ t : ℝ, (∑ b, (exp ((t : ℂ) • A)) a b /
        ((t : ℂ) ^ 0 * Complex.exp (μ * t)) * z b) = z a := by
      intro t
      have h1 := congrFun (exp_smul_mulVec_of_mulVec_eq_smul A hz (t : ℂ)) a
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
      have he : Complex.exp ((μ : ℂ) * t) ≠ 0 := Complex.exp_ne_zero _
      rw [pow_zero, one_mul]
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, h1, mul_div_cancel_left₀ _ he]
    simp only [hconst] at hsum
    exact ha (tendsto_nhds_unique tendsto_const_nhds hsum)
  -- let `k` be the largest such `j`
  obtain ⟨j₀, hj₀N, hj₀⟩ := hex
  have hne : ((Finset.range (Fintype.card n)).filter fun j => C μ j ≠ 0).Nonempty :=
    ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj₀N, hj₀⟩⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image _ id hne
  rw [Finset.mem_filter, Finset.mem_range] at hk
  refine ⟨k, C μ k, hk.2, key k hk.1 fun j hkj hjN => ?_⟩
  by_contra hCj
  have := hkmax j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjN, hCj⟩)
  simp only [id] at this
  omega

/-- **Step 3**, equation (L): if `μ` is a real eigenvalue of the real matrix `B` and every other
(complex) eigenvalue of `B` has real part `< μ`, then there are `k` and a nonzero real matrix `L`
with `lim_{t → ∞} e^{Bt} / (t^k e^{μ t}) = L`. -/
theorem exists_leading_term_real (B : Matrix n n ℝ) (μ : ℝ)
    (hμ : (μ : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)))
    (hdom : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam ≠ (μ : ℂ) → lam.re < μ) :
    ∃ (k : ℕ) (L : Matrix n n ℝ), L ≠ 0 ∧ ∀ a b,
      Tendsto (fun t : ℝ => (exp (t • B)) a b / (t ^ k * Real.exp (μ * t))) atTop
        (𝓝 (L a b)) := by
  obtain ⟨k, Lc, hLc0, hLc⟩ := exists_leading_term (B.map (algebraMap ℝ ℂ)) μ hμ hdom
  -- the complex quotient is the real quotient
  have hcast : ∀ (a b : n) (t : ℝ),
      (exp ((t : ℂ) • B.map (algebraMap ℝ ℂ))) a b / ((t : ℂ) ^ k * Complex.exp (μ * t)) =
        (((exp (t • B)) a b / (t ^ k * Real.exp (μ * t)) : ℝ) : ℂ) := by
    intro a b t
    rw [← ofReal_exp_smul_apply]
    push_cast
    rfl
  have hlim : ∀ a b, Tendsto (fun t : ℝ =>
      (((exp (t • B)) a b / (t ^ k * Real.exp (μ * t)) : ℝ) : ℂ)) atTop (𝓝 (Lc a b)) := by
    intro a b
    exact (hLc a b).congr fun t => hcast a b t
  -- hence the limit is real
  have him : ∀ a b, (Lc a b).im = 0 := by
    intro a b
    have h := (Complex.continuous_im.tendsto (Lc a b)).comp (hlim a b)
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  refine ⟨k, Matrix.of fun a b => (Lc a b).re, ?_, fun a b => ?_⟩
  · intro hzero
    apply hLc0
    ext a b
    have hre : (Lc a b).re = 0 := by
      have := congrFun (congrFun hzero a) b
      simpa using this
    exact Complex.ext hre (him a b)
  · have h := (Complex.continuous_re.tendsto (Lc a b)).comp (hlim a b)
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h

end PosLinearSys
