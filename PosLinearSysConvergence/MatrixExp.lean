import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# Lemma 3 (the matrix exponential)

The facts about `e^{At}` used by the proof of Theorem 2 of the text. Mathlib's matrix
exponential is `NormedSpace.exp`, and `e^{At}` is written `exp (t • A)`.

* Lemma 3 (a): `hasDerivAt_exp_smul`, `hasDerivAt_exp_smul_mulVec`, and the "hence" part
  `eq_exp_smul_mulVec_of_hasDerivWithinAt` (a solution of `ẋ = A x` on `[0, ∞)` is
  `e^{At} x(0)`), with the variant `eq_exp_smul_mulVec_of_continuousOn`.
* Lemma 3 (b): `exp_add_smul`.
* Lemma 3 (c): `exp_smul_add_smul_one` (real) and `exp_smul_eq_cexp_smul` (complex).
* Lemma 3 (d): `exp_smul_mulVec_of_mulVec_eq_smul`.

The statements do not mention a matrix norm; an operator norm is chosen inside the proofs where
Mathlib's lemmas need one.
-/

namespace PosLinearSys

open Matrix NormedSpace Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Real matrices -/

/-- Lemma 3 (a): `d/dt e^{At} = A e^{At}`. -/
theorem hasDerivAt_exp_smul (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t := by
  open scoped Matrix.Norms.Operator in
  exact hasDerivAt_exp_smul_const' A t

/-- Lemma 3 (a), entrywise. -/
theorem hasDerivAt_exp_smul_apply (A : Matrix n n ℝ) (t : ℝ) (a b : n) :
    HasDerivAt (fun s : ℝ => (exp (s • A)) a b) ((A * exp (t • A)) a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_exp_smul A t) a) b

/-- `A` commutes with `e^{At}`. -/
theorem commute_exp_smul (A : Matrix n n ℝ) (t : ℝ) : Commute A (exp (t • A)) :=
  ((Commute.refl A).smul_right t).exp_right

/-- Lemma 3 (a) applied to a vector: `d/dt (e^{At} v) = A (e^{At} v)`. -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix n n ℝ) (v : n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) *ᵥ v) (A *ᵥ (exp (t • A) *ᵥ v)) t := by
  rw [hasDerivAt_pi]
  intro a
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    fun b (_ : b ∈ Finset.univ) => (hasDerivAt_exp_smul_apply A t a b).mul_const (v b)
  rw [Matrix.mulVec_mulVec]
  exact h

/-- Lemma 3 (a): `e^{A·0} = I`. -/
theorem exp_zero_smul (A : Matrix n n ℝ) : exp ((0 : ℝ) • A) = 1 := by
  rw [zero_smul, exp_zero]

/-- Lemma 3 (b): `e^{A(s+t)} = e^{As} e^{At}`. -/
theorem exp_add_smul (A : Matrix n n ℝ) (s t : ℝ) :
    exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t)

theorem exp_smul_one_real (r : ℝ) :
    exp (r • (1 : Matrix n n ℝ)) = Real.exp r • (1 : Matrix n n ℝ) := by
  have h : algebraMap ℝ (Matrix n n ℝ) (exp r) = exp (algebraMap ℝ (Matrix n n ℝ) r) := by
    open scoped Matrix.Norms.Operator in
    exact algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
  rw [← h, Real.exp_eq_exp_ℝ]

/-- Lemma 3 (c), for a real shift `c`: `e^{(A + cI)t} = e^{ct} e^{At}`. -/
theorem exp_smul_add_smul_one (A : Matrix n n ℝ) (c t : ℝ) :
    exp (t • (A + c • (1 : Matrix n n ℝ))) = Real.exp (c * t) • exp (t • A) := by
  rw [smul_add, smul_smul,
    Matrix.exp_add_of_commute _ _ ((Commute.one_right (t • A)).smul_right (t * c)),
    exp_smul_one_real, mul_smul_comm, mul_one, mul_comm t c]

/-- Lemma 3 (a), the "hence" part: a solution `x` of `ẋ = A x` on `[0, ∞)` (with a one-sided
derivative at `0`) is `x t = e^{At} x(0)`. -/
theorem eq_exp_smul_mulVec_of_hasDerivWithinAt (A : Matrix n n ℝ) (x : ℝ → n → ℝ)
    (hx : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Set.Ici 0) t) :
    ∀ t ∈ Set.Ici (0 : ℝ), x t = exp (t • A) *ᵥ x 0 := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  -- the vector field `y ↦ A y` is Lipschitz
  obtain ⟨K, hK⟩ : ∃ K : NNReal, LipschitzWith K (fun y : n → ℝ => A *ᵥ y) := by
    refine ⟨‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)‖₊, ?_⟩
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitzWith
  have hxc : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
    ((hx s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have hx' : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt x (A *ᵥ x s) (Set.Ici s) s := fun s hs =>
    (hx s hs.1).mono (Set.Ici_subset_Ici.2 hs.1)
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => exp (s • A) *ᵥ x 0)
      (A *ᵥ (exp (s • A) *ᵥ x 0)) s := fun s => hasDerivAt_exp_smul_mulVec A (x 0) s
  have hgc : ContinuousOn (fun s : ℝ => exp (s • A) *ᵥ x 0) (Set.Icc 0 t) := fun s _ =>
    (hg s).continuousAt.continuousWithinAt
  have h0 : x 0 = exp ((0 : ℝ) • A) *ᵥ x 0 := by
    rw [exp_zero_smul, Matrix.one_mulVec]
  exact ODE_solution_unique (v := fun _ y => A *ᵥ y) (fun _ => hK) hxc hx' hgc
    (fun s _ => (hg s).hasDerivWithinAt) h0 ⟨ht0, le_rfl⟩

/-- `t ↦ e^{At}` is continuous. -/
theorem continuous_exp_smul (A : Matrix n n ℝ) : Continuous fun s : ℝ => exp (s • A) :=
  continuous_matrix fun a b =>
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_apply A s a b).continuousAt

/-- A variant of `eq_exp_smul_mulVec_of_hasDerivWithinAt` under the weakest notion of solution:
if `x` is continuous on `[0, ∞)` and satisfies `ẋ = A x` on `(0, ∞)`, then `x t = e^{At} x(0)`
for `t ≥ 0`. -/
theorem eq_exp_smul_mulVec_of_continuousOn (A : Matrix n n ℝ) (x : ℝ → n → ℝ)
    (hc : ContinuousOn x (Set.Ici 0)) (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A *ᵥ x t) t) :
    ∀ t ∈ Set.Ici (0 : ℝ), x t = exp (t • A) *ᵥ x 0 := by
  intro t ht
  rcases (Set.mem_Ici.1 ht).eq_or_lt with h0 | hpos
  · rw [← h0, exp_zero_smul, Matrix.one_mulVec]
  -- from any time `ε ∈ (0, t]` on, `x` is given by the exponential
  have hε : ∀ ε : ℝ, 0 < ε → ε ≤ t → x t = exp ((t - ε) • A) *ᵥ x ε := by
    intro ε hε hεt
    have h := eq_exp_smul_mulVec_of_hasDerivWithinAt A (fun s : ℝ => x (ε + s))
      (fun s hs => ((hx (ε + s) (add_pos_of_pos_of_nonneg hε (Set.mem_Ici.1 hs))).comp_const_add
        ε s).hasDerivWithinAt)
      (t - ε) (Set.mem_Ici.2 (sub_nonneg.2 hεt))
    simpa using h
  -- now let `ε → 0⁺`
  have h1 : Tendsto (fun ε : ℝ => exp ((t - ε) • A)) (𝓝[>] 0) (𝓝 (exp ((t - 0) • A))) :=
    (((continuous_exp_smul A).comp (continuous_const.sub continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto x (𝓝[>] 0) (𝓝 (x 0)) :=
    (hc 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self
  have h3 : Tendsto (fun ε : ℝ => exp ((t - ε) • A) *ᵥ x ε) (𝓝[>] 0)
      (𝓝 (exp ((t - 0) • A) *ᵥ x 0)) :=
    ((continuous_fst.matrix_mulVec continuous_snd).tendsto (exp ((t - 0) • A), x 0)).comp
      (h1.prodMk_nhds h2)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x t = exp ((t - ε) • A) *ᵥ x ε := by
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε'
    exact hε ε hε'.1 hε'.2.le
  have h4 := tendsto_nhds_unique (tendsto_const_nhds.congr' heq) h3
  rw [h4, sub_zero]

/-! ### Complex matrices -/

theorem exp_smul_one_complex (r : ℂ) :
    exp (r • (1 : Matrix n n ℂ)) = Complex.exp r • (1 : Matrix n n ℂ) := by
  have h : algebraMap ℂ (Matrix n n ℂ) (exp r) = exp (algebraMap ℂ (Matrix n n ℂ) r) := by
    open scoped Matrix.Norms.Operator in
    exact algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := Matrix n n ℂ) r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
  rw [← h, Complex.exp_eq_exp_ℂ]

/-- Lemma 3 (c), for a complex shift: `e^{At} = e^{lam t} e^{(A - lam I)t}`. -/
theorem exp_smul_eq_cexp_smul (A : Matrix n n ℂ) (lam t : ℂ) :
    exp (t • A) = Complex.exp (lam * t) • exp (t • (A - lam • (1 : Matrix n n ℂ))) := by
  have h : t • A = t • (A - lam • (1 : Matrix n n ℂ)) + (t * lam) • (1 : Matrix n n ℂ) := by
    rw [smul_sub, smul_smul, sub_add_cancel]
  rw [h, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right (t * lam)),
    exp_smul_one_complex, mul_smul_comm, mul_one, mul_comm t lam]

/-- If `D ^ N` kills `v`, then `e^{Dt} v` is the finite sum `∑_{j<N} t^j / j! · D^j v`. -/
theorem exp_smul_mulVec_of_pow_mulVec_eq_zero (D : Matrix n n ℂ) (v : n → ℂ) (N : ℕ)
    (h : (D ^ N) *ᵥ v = 0) (t : ℂ) :
    exp (t • D) *ᵥ v =
      ∑ j ∈ Finset.range N, ((j.factorial : ℂ)⁻¹ * t ^ j) • ((D ^ j) *ᵥ v) := by
  have hsum : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (t • D) ^ k) (exp (t • D)) := by
    open scoped Matrix.Norms.Operator in
    exact exp_series_hasSum_exp' (𝕂 := ℂ) (t • D)
  have hcont : Continuous (Matrix.mulVec.addMonoidHomLeft v : Matrix n n ℂ →+ n → ℂ) :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have hsum' : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ * t ^ k) • ((D ^ k) *ᵥ v))
      (exp (t • D) *ᵥ v) := by
    have h2 := hsum.map (Matrix.mulVec.addMonoidHomLeft v) hcont
    have hfun : ((Matrix.mulVec.addMonoidHomLeft v : Matrix n n ℂ →+ n → ℂ) ∘
        fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (t • D) ^ k) =
        fun k => ((k.factorial : ℂ)⁻¹ * t ^ k) • ((D ^ k) *ᵥ v) := by
      funext k
      change (((k.factorial : ℂ)⁻¹) • (t • D) ^ k) *ᵥ v = _
      rw [smul_pow, smul_smul, Matrix.smul_mulVec]
    rw [hfun] at h2
    exact h2
  have hzero : ∀ k ∉ Finset.range N,
      ((k.factorial : ℂ)⁻¹ * t ^ k) • ((D ^ k) *ᵥ v) = 0 := by
    intro k hk
    have hNk : N ≤ k := by simpa using hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNk
    have hDk : (D ^ (N + m)) *ᵥ v = 0 := by
      rw [add_comm, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    rw [hDk, smul_zero]
  exact hsum'.unique (hasSum_sum_of_ne_finset_zero hzero)

/-- Lemma 3 (d): if `A u = lam u` then `e^{At} u = e^{lam t} u`. -/
theorem exp_smul_mulVec_of_mulVec_eq_smul (A : Matrix n n ℂ) {lam : ℂ} {u : n → ℂ}
    (hu : A *ᵥ u = lam • u) (t : ℂ) :
    exp (t • A) *ᵥ u = Complex.exp (lam * t) • u := by
  have h1 : ((A - lam • (1 : Matrix n n ℂ)) ^ 1) *ᵥ u = 0 := by
    rw [pow_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hu, sub_self]
  rw [exp_smul_eq_cexp_smul A lam t, Matrix.smul_mulVec,
    exp_smul_mulVec_of_pow_mulVec_eq_zero _ u 1 h1 t]
  simp

/-! ### From real to complex matrices -/

/-- The entrywise inclusion `ℝ → ℂ` commutes with the matrix exponential. -/
theorem exp_smul_map_ofReal (B : Matrix n n ℝ) (t : ℝ) :
    (exp (t • B)).map (algebraMap ℝ ℂ) = exp ((t : ℂ) • B.map (algebraMap ℝ ℂ)) := by
  have hcont : Continuous ((algebraMap ℝ ℂ).mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ) :=
    Continuous.matrix_map continuous_id Complex.continuous_ofReal
  have h : (algebraMap ℝ ℂ).mapMatrix (exp (t • B)) =
      exp ((algebraMap ℝ ℂ).mapMatrix (t • B)) := by
    open scoped Matrix.Norms.Operator in
    exact map_exp ((algebraMap ℝ ℂ).mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ) hcont (t • B)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext i j
  simp

/-- Entrywise form of `exp_smul_map_ofReal`. -/
theorem ofReal_exp_smul_apply (B : Matrix n n ℝ) (t : ℝ) (a b : n) :
    (((exp (t • B)) a b : ℝ) : ℂ) = (exp ((t : ℂ) • B.map (algebraMap ℝ ℂ))) a b := by
  rw [← exp_smul_map_ofReal]
  rfl

end PosLinearSys
