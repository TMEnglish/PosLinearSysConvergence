import PosLinearSysConvergence.Positivity
import PosLinearSysConvergence.Modes
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Lemma 5 (Perron–Frobenius for Metzler matrices)

`exists_dominant_eigenvalue` is Lemma 5 of the text: for a Metzler matrix `B`, the largest
real part `μ` of an eigenvalue of `B` is itself an eigenvalue of `B`, and every eigenvalue
`lam ≠ μ` has `Re lam < μ`.

Mathlib has no Perron–Frobenius theory, so the lemma is proved from Step 1 (`e^{Bt} ≥ 0`) and
Lemma 4. The proof follows parts (i)–(v) of the proof in the text:

* (i) `e^{At} ≥ 0` for a Metzler matrix `A` and `t ≥ 0`: this is `exp_smul_apply_nonneg`, in
  `Positivity.lean`.
* (ii) `nonneg_of_mulVec_nonpos` (inverse positivity): if `A` is Metzler, all its eigenvalues have
  negative real part, and `A d ≤ 0`, then `d ≥ 0`. Indeed `t ↦ e^{At} d` has derivative
  `e^{At} (A d) ≤ 0`, so it is nonincreasing, and it tends to `0`.
* (iii) `le_of_mul_le_mulVec`: if `w ≥ 0` is nonzero and `B w ≥ r w`, then `r ≤ σ` for every
  bound `σ` on the real parts of the eigenvalues of `B`.
* (iv) `norm_add_sub_mul_le_mulVec`: for an eigenvector `z` of `B` with eigenvalue `lam`, the
  vector `|z|` of moduli satisfies `B |z| ≥ (|lam + c| - c) |z|` whenever `B + cI ≥ 0`.
* (v) `exists_dominant_eigenvalue`: hence `|lam + c| ≤ μ + c`, and if `Re lam = μ` this forces
  `lam = μ`.
-/

namespace PosLinearSys

open Matrix NormedSpace Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Shifting the diagonal -/

omit [Fintype n] in
/-- Subtracting a multiple of the identity from a Metzler matrix gives a Metzler matrix. -/
theorem IsMetzler.sub_smul_one {A : Matrix n n ℝ} (hA : IsMetzler A) (r : ℝ) :
    IsMetzler (A - r • (1 : Matrix n n ℝ)) := by
  intro i j hij
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
    mul_zero, sub_zero]
  exact hA i j hij

theorem map_sub_smul_one (B : Matrix n n ℝ) (r : ℝ) :
    (B - r • (1 : Matrix n n ℝ)).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix n n ℂ) (-(r : ℂ)) + B.map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.algebraMap_matrix_apply]
    ring
  · simp [Matrix.algebraMap_matrix_apply, hij]

/-- The eigenvalues of `B - rI` are the eigenvalues of `B`, shifted by `r`. -/
theorem add_mem_spectrum_of_mem_spectrum_sub {B : Matrix n n ℝ} {r : ℝ} {lam : ℂ}
    (h : lam ∈ spectrum ℂ ((B - r • (1 : Matrix n n ℝ)).map (algebraMap ℝ ℂ))) :
    lam + r ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
  rw [map_sub_smul_one] at h
  have hlam : lam = (lam + r) + (-(r : ℂ)) := by ring
  rw [hlam] at h
  exact spectrum.add_mem_add_iff.1 h

/-- A real number is an eigenvalue of the real matrix `B` exactly when it is an eigenvalue of `B`
regarded as a complex matrix. -/
theorem ofReal_mem_spectrum_map_iff (B : Matrix n n ℝ) (r : ℝ) :
    (r : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) ↔ r ∈ spectrum ℝ B := by
  rw [spectrum.mem_iff, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have h : algebraMap ℂ (Matrix n n ℂ) (r : ℂ) - B.map (algebraMap ℝ ℂ) =
      (algebraMap ℝ ℂ).mapMatrix (algebraMap ℝ (Matrix n n ℝ) r - B) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_matrix_apply]
    · simp [Matrix.algebraMap_matrix_apply, hij]
  rw [h, ← RingHom.map_det]
  simp

/-! ### Inverse positivity -/

/-- Lemma 5, part (ii): inverse positivity. If `A` is Metzler, every eigenvalue of `A` has
negative real part, and `A d ≤ 0`, then `d ≥ 0`. -/
theorem nonneg_of_mulVec_nonpos {A : Matrix n n ℝ} (hA : IsMetzler A)
    (hspec : ∀ lam ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), lam.re < 0) {d : n → ℝ}
    (hd : ∀ i, (A *ᵥ d) i ≤ 0) (i : n) : 0 ≤ d i := by
  -- `ψ t = (e^{At} d)_i` has derivative `(e^{At} (A d))_i ≤ 0` for `t ≥ 0`
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (exp (s • A) *ᵥ d) i)
      ((exp (t • A) *ᵥ (A *ᵥ d)) i) t := by
    intro t
    have h := hasDerivAt_pi.1 (hasDerivAt_exp_smul_mulVec A d t) i
    rwa [Matrix.mulVec_mulVec, (commute_exp_smul A t).eq, ← Matrix.mulVec_mulVec] at h
  have hnonpos : ∀ t : ℝ, 0 ≤ t → (exp (t • A) *ᵥ (A *ᵥ d)) i ≤ 0 := by
    intro t ht
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (exp_smul_apply_nonneg hA ht i j) (hd j)
  have hanti : AntitoneOn (fun s : ℝ => (exp (s • A) *ᵥ d) i) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
      (fun s _ => (hderiv s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hderiv s).deriv]
    exact hnonpos s (le_of_lt hs)
  -- and it tends to `0`
  have hlim : Tendsto (fun s : ℝ => (exp (s • A) *ᵥ d) i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) =>
      (tendsto_exp_smul_apply_zero A hspec i j).mul_const (d j)
    simp only [zero_mul, Finset.sum_const_zero] at h
    exact h
  have h0 : (exp ((0 : ℝ) • A) *ᵥ d) i = d i := by
    rw [exp_zero_smul, Matrix.one_mulVec]
  rw [← h0]
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht

/-- Lemma 5, part (iii): a comparison. If `B` is Metzler, `μ` bounds the real parts of the
eigenvalues of `B`, and `w ≥ 0` is a nonzero vector with `B w ≥ r w`, then `r ≤ μ`. (The text
calls the bound `σ`.) -/
theorem le_of_mul_le_mulVec {B : Matrix n n ℝ} (hB : IsMetzler B) {μ : ℝ}
    (hμ : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam.re ≤ μ) {w : n → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : w ≠ 0) {r : ℝ} (hr : ∀ i, r * w i ≤ (B *ᵥ w) i) : r ≤ μ := by
  by_contra hlt
  have hlt' : μ < r := not_le.1 hlt
  have hspec : ∀ lam ∈ spectrum ℂ ((B - r • (1 : Matrix n n ℝ)).map (algebraMap ℝ ℂ)),
      lam.re < 0 := by
    intro lam hlam
    have h := hμ _ (add_mem_spectrum_of_mem_spectrum_sub hlam)
    rw [Complex.add_re, Complex.ofReal_re] at h
    linarith
  have hd : ∀ i, ((B - r • (1 : Matrix n n ℝ)) *ᵥ (-w)) i ≤ 0 := by
    intro i
    rw [Matrix.mulVec_neg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hr i]
  have hnonneg := nonneg_of_mulVec_nonpos (hB.sub_smul_one r) hspec hd
  apply hw
  funext i
  have h1 := hnonneg i
  rw [Pi.neg_apply] at h1
  change w i = 0
  exact le_antisymm (by linarith) (hw0 i)

/-! ### Moduli of an eigenvector -/

/-- Lemma 5, part (iv): moduli of an eigenvector. Let `z` be an eigenvector, with eigenvalue
`lam`, of the matrix `B` (regarded as a complex matrix), and let `B + cI ≥ 0`. Then the vector
`|z|` of moduli satisfies `(|lam + c| - c) |z| ≤ B |z|`. -/
theorem norm_add_sub_mul_le_mulVec {B : Matrix n n ℝ} {c : ℝ}
    (hP : ∀ i j, 0 ≤ (B + c • (1 : Matrix n n ℝ)) i j) {lam : ℂ} {z : n → ℂ}
    (hz : B.map (algebraMap ℝ ℂ) *ᵥ z = lam • z) (i : n) :
    (‖lam + c‖ - c) * ‖z i‖ ≤ (B *ᵥ fun j => ‖z j‖) i := by
  -- `(lam + c) z_i = ∑_j P_ij z_j`
  have h1 : (lam + c) * z i = ∑ j, (((B + c • (1 : Matrix n n ℝ)) i j : ℝ) : ℂ) * z j := by
    have hzi : ∑ j, ((B i j : ℝ) : ℂ) * z j = lam * z i := congrFun hz i
    have hc : ∑ j, (((c • (1 : Matrix n n ℝ)) i j : ℝ) : ℂ) * z j = c * z i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Matrix.one_apply_ne (Ne.symm hji)]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp only [Matrix.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
    rw [hzi, hc]
  have h2 : ‖lam + c‖ * ‖z i‖ ≤ ∑ j, (B + c • (1 : Matrix n n ℝ)) i j * ‖z j‖ := by
    rw [← norm_mul, h1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP i j)]
  have h3 : ∑ j, (B + c • (1 : Matrix n n ℝ)) i j * ‖z j‖ =
      (B *ᵥ fun j => ‖z j‖) i + c * ‖z i‖ := by
    have h : ((B + c • (1 : Matrix n n ℝ)) *ᵥ fun j => ‖z j‖) i =
        (B *ᵥ fun j => ‖z j‖) i + c * ‖z i‖ := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    exact h
  have h4 : (‖lam + c‖ - c) * ‖z i‖ = ‖lam + c‖ * ‖z i‖ - c * ‖z i‖ := by ring
  linarith

/-! ### Lemma 5 -/

/-- **Lemma 5** (Perron–Frobenius for Metzler matrices). Let `B` be a Metzler matrix (of positive
size). There is a real number `μ` which is an eigenvalue of `B` and such that every eigenvalue
`lam ≠ μ` of `B` satisfies `Re lam < μ`. (So `μ` is the largest real part of an eigenvalue of
`B`; see `isGreatest_re_spectrum`.) No irreducibility is assumed. -/
theorem exists_dominant_eigenvalue [Nonempty n] {B : Matrix n n ℝ} (hB : IsMetzler B) :
    ∃ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) ∧
      ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam ≠ (μ : ℂ) → lam.re < μ := by
  have hne : (spectrum ℂ (B.map (algebraMap ℝ ℂ))).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _
  -- an eigenvalue `lam₀` of largest real part
  obtain ⟨lam₀, hlam₀, hmax⟩ := Set.exists_max_image (spectrum ℂ (B.map (algebraMap ℝ ℂ)))
    Complex.re (Matrix.finite_spectrum _) hne
  -- an eigenvalue whose real part is the largest one is real
  have key : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam.re = lam₀.re →
      lam = (lam₀.re : ℂ) := by
    intro lam hlam hre
    obtain ⟨z, hz0, hz⟩ := exists_eigenvector_of_mem_spectrum _ hlam
    have hw : (fun j => ‖z j‖) ≠ (0 : n → ℝ) := by
      intro h
      apply hz0
      funext j
      simpa using congrFun h j
    have hle : ‖lam + (shiftConst B : ℂ)‖ - shiftConst B ≤ lam₀.re :=
      le_of_mul_le_mulVec hB hmax (fun j => norm_nonneg (z j)) hw
        (norm_add_sub_mul_le_mulVec (add_shiftConst_apply_nonneg hB) hz)
    have h1 : ‖lam + (shiftConst B : ℂ)‖ ≤ (lam + (shiftConst B : ℂ)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith
    have h2 : ‖lam + (shiftConst B : ℂ)‖ ^ 2 =
        (lam + (shiftConst B : ℂ)).re ^ 2 + (lam + (shiftConst B : ℂ)).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h3 : ‖lam + (shiftConst B : ℂ)‖ ^ 2 ≤ (lam + (shiftConst B : ℂ)).re ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 : (lam + (shiftConst B : ℂ)).im ^ 2 ≤ 0 := by linarith
    have h5 : (lam + (shiftConst B : ℂ)).im = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 (sq_nonneg _))
    have him : lam.im = 0 := by
      rwa [Complex.add_im, Complex.ofReal_im, add_zero] at h5
    exact Complex.ext (by rw [Complex.ofReal_re, hre]) (by rw [Complex.ofReal_im, him])
  refine ⟨lam₀.re, ?_, fun lam hlam hne' => ?_⟩
  · rw [← key lam₀ hlam₀ rfl]
    exact hlam₀
  · exact lt_of_le_of_ne (hmax lam hlam) fun h => hne' (key lam hlam h)

/-- The number `μ` of Lemma 5 is the largest real part of an eigenvalue of `B`. -/
theorem isGreatest_re_spectrum {B : Matrix n n ℝ} {μ : ℝ}
    (hμ : (μ : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)))
    (hdom : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam ≠ (μ : ℂ) → lam.re < μ) :
    IsGreatest (Complex.re '' spectrum ℂ (B.map (algebraMap ℝ ℂ))) μ := by
  refine ⟨⟨(μ : ℂ), hμ, Complex.ofReal_re μ⟩, ?_⟩
  rintro _ ⟨lam, hlam, rfl⟩
  by_cases h : lam = (μ : ℂ)
  · rw [h, Complex.ofReal_re]
  · exact (hdom lam hlam h).le

end PosLinearSys
