import PosLinearSysConvergence.PerronFrobenius

/-!
# Theorem 2

Formalization of Theorem 2 of the text: if `M` is a Metzler matrix and `x` solves
`ẋ = M x` on `[0, ∞)` from a nonnegative, nonzero initial state, then the normalized solution
`x(t) / ∑ᵢ xᵢ(t)` converges to a nonnegative eigenvector of `M`.

The main statement is `PosLinearSys.tendsto_normalized_solution`. The file follows Steps 2–6 of
the text:

* Step 2: `exp_smul_mulVec_pos`, `exp_smul_mulVec_eq_zero`, `sum_exp_smul_mulVec_pos`,
  `restrict_exp_smul_mulVec` (the reduced system);
* Step 3 is `exists_leading_term_real` (in `Modes.lean`);
* Step 4: `leading_nonneg`, `exp_smul_mul_leading`, `mul_leading_eq`;
* Step 5: `tendsto_normalized_of_pos`;
* Step 6: the proof of `tendsto_normalized_solution`.

`tendsto_normalized_solution_of_hasDerivAt`, `tendsto_normalized_solution_of_continuousOn` and
`tendsto_normalized_solution_exp` restate the theorem for other ways of saying that `x` is the
solution of `ẋ = M x`.
-/

namespace PosLinearSys

open Matrix NormedSpace Filter Topology

/-! ## Steps 4 and 5: the limit for a Metzler matrix `B` -/

section Reduced

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Step 4 (i): the limit matrix `L` is nonnegative. -/
theorem leading_nonneg {B : Matrix n n ℝ} (hB : IsMetzler B) {μ : ℝ} {k : ℕ} {L : Matrix n n ℝ}
    (hL : ∀ a b, Tendsto (fun t : ℝ => (exp (t • B)) a b / (t ^ k * Real.exp (μ * t))) atTop
      (𝓝 (L a b))) (a b : n) : 0 ≤ L a b := by
  refine ge_of_tendsto (hL a b) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact div_nonneg (exp_smul_apply_nonneg hB ht a b)
    (mul_nonneg (pow_nonneg ht k) (Real.exp_pos _).le)

/-- Step 4 (ii), equation (semigroup): `e^{Bs} L = e^{μ s} L`. (The text takes `s > 0`; the same
computation works for every real `s`.) -/
theorem exp_smul_mul_leading {B : Matrix n n ℝ} {μ : ℝ} {k : ℕ} {L : Matrix n n ℝ}
    (hL : ∀ a b, Tendsto (fun t : ℝ => (exp (t • B)) a b / (t ^ k * Real.exp (μ * t))) atTop
      (𝓝 (L a b))) (s : ℝ) : exp (s • B) * L = Real.exp (μ * s) • L := by
  ext a b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  -- the left side as a limit
  have h1 : Tendsto (fun t : ℝ => ∑ c, (exp (s • B)) a c *
      ((exp (t • B)) c b / (t ^ k * Real.exp (μ * t)))) atTop
      (𝓝 (∑ c, (exp (s • B)) a c * L c b)) :=
    tendsto_finsetSum _ fun c _ => (hL c b).const_mul _
  -- the right side as a limit
  have hshift : Tendsto (fun t : ℝ => s + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop s tendsto_id
  have h2 : Tendsto (fun t : ℝ => (exp ((s + t) • B)) a b /
      ((s + t) ^ k * Real.exp (μ * (s + t)))) atTop (𝓝 (L a b)) := (hL a b).comp hshift
  have hratio : Tendsto (fun t : ℝ => (s + t) / t) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := s) (f := (atTop : Filter ℝ))).div_atTop tendsto_id
    have h' : Tendsto (fun t : ℝ => s / t + 1) atTop (𝓝 (0 + 1)) := h.add tendsto_const_nhds
    rw [zero_add] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have h3 : Tendsto (fun t : ℝ => ((s + t) / t) ^ k * Real.exp (μ * s)) atTop
      (𝓝 (1 ^ k * Real.exp (μ * s))) := (hratio.pow k).mul_const _
  have h4 := h3.mul h2
  -- the two functions agree for large `t`
  have heq : ∀ᶠ t : ℝ in atTop,
      ((s + t) / t) ^ k * Real.exp (μ * s) *
        ((exp ((s + t) • B)) a b / ((s + t) ^ k * Real.exp (μ * (s + t)))) =
      ∑ c, (exp (s • B)) a c * ((exp (t • B)) c b / (t ^ k * Real.exp (μ * t))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-s)] with t ht hts
    have hst : s + t ≠ 0 := by linarith
    have ht' : t ≠ 0 := ht.ne'
    have hsum : (exp ((s + t) • B)) a b = ∑ c, (exp (s • B)) a c * (exp (t • B)) c b := by
      rw [exp_add_smul, Matrix.mul_apply]
    have hsum' : ∑ c, (exp (s • B)) a c * ((exp (t • B)) c b / (t ^ k * Real.exp (μ * t))) =
        (exp ((s + t) • B)) a b / (t ^ k * Real.exp (μ * t)) := by
      rw [hsum, Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by rw [mul_div_assoc]
    rw [hsum', mul_add, Real.exp_add, div_pow]
    field_simp
  have h5 := tendsto_nhds_unique (h4.congr' heq) h1
  rw [← h5, one_pow, one_mul]

/-- Step 4 (ii), equation (eig): `B L = μ L`. -/
theorem mul_leading_eq {B : Matrix n n ℝ} {μ : ℝ} {k : ℕ} {L : Matrix n n ℝ}
    (hL : ∀ a b, Tendsto (fun t : ℝ => (exp (t • B)) a b / (t ^ k * Real.exp (μ * t))) atTop
      (𝓝 (L a b))) : B * L = μ • L := by
  ext a b
  -- differentiate `e^{Bs} L = e^{μ s} L` at `s = 0`
  have hd1 : HasDerivAt (fun s : ℝ => (exp (s • B) * L) a b) ((B * L) a b) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun c (_ : c ∈ Finset.univ) =>
      (hasDerivAt_exp_smul_apply B 0 a c).mul_const (L c b)
    rw [exp_zero_smul, mul_one] at h
    exact h
  have hd2 : HasDerivAt (fun s : ℝ => (Real.exp (μ * s) • L) a b) ((μ • L) a b) 0 := by
    have h : HasDerivAt (fun s : ℝ => Real.exp (μ * s)) (Real.exp (μ * 0) * (μ * 1)) 0 :=
      (Real.hasDerivAt_exp (μ * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul μ)
    rw [mul_zero, Real.exp_zero, one_mul, mul_one] at h
    exact h.mul_const (L a b)
  have hfun : (fun s : ℝ => (exp (s • B) * L) a b) = fun s : ℝ => (Real.exp (μ * s) • L) a b :=
    funext fun s => by rw [exp_smul_mul_leading hL s]
  rw [hfun] at hd1
  exact hd1.unique hd2

/-- **Steps 3–5** for a Metzler matrix `B` with dominant eigenvalue `μ` (Lemma 5): if
`y(t) = e^{Bt} y₀` is strictly positive at some time `τ`, then `y(t) / ∑ᵢ yᵢ(t)` converges to a
vector `q ≥ 0` with `∑ᵢ qᵢ = 1` and `B q = μ q`. -/
theorem tendsto_normalized_of_pos {B : Matrix n n ℝ} (hB : IsMetzler B) {μ : ℝ}
    (hμ : (μ : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)))
    (hdom : ∀ lam ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), lam ≠ (μ : ℂ) → lam.re < μ)
    (y₀ : n → ℝ) {τ : ℝ} (hτ : ∀ i, 0 < (exp (τ • B) *ᵥ y₀) i) :
    ∃ q : n → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ B *ᵥ q = μ • q ∧
      Tendsto (fun t : ℝ => (∑ i, (exp (t • B) *ᵥ y₀) i)⁻¹ • (exp (t • B) *ᵥ y₀)) atTop
        (𝓝 q) := by
  -- Step 3: the leading term `L` of `e^{Bt}`; Step 4: `L ≥ 0` and `B L = μ L`
  obtain ⟨k, L, hL0, hL⟩ := exists_leading_term_real B μ hμ hdom
  have hLnn := leading_nonneg hB hL
  have hBL := mul_leading_eq hL
  -- Step 5: `z = y(τ)` and `v = L z`
  obtain ⟨z, hz⟩ : ∃ z : n → ℝ, z = exp (τ • B) *ᵥ y₀ := ⟨_, rfl⟩
  have hzpos : ∀ i, 0 < z i := fun i => by rw [hz]; exact hτ i
  obtain ⟨v, hv⟩ : ∃ v : n → ℝ, v = L *ᵥ z := ⟨_, rfl⟩
  have hv0 : ∀ a, 0 ≤ v a := fun a => by
    rw [hv]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hLnn a b) (hzpos b).le
  -- Step 4 (iii): `v ≠ 0`, in the form `∑ v > 0`
  have hvpos : 0 < ∑ a, v a := by
    obtain ⟨a, b, hab⟩ : ∃ a b, L a b ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hL0 (Matrix.ext h)
    have hLab : 0 < L a b := lt_of_le_of_ne (hLnn a b) (Ne.symm hab)
    have hva : 0 < v a := by
      rw [hv]
      exact lt_of_lt_of_le (mul_pos hLab (hzpos b))
        (Finset.single_le_sum (f := fun b => L a b * z b)
          (fun b _ => mul_nonneg (hLnn a b) (hzpos b).le) (Finset.mem_univ b))
    exact lt_of_lt_of_le hva
      (Finset.single_le_sum (f := v) (fun a _ => hv0 a) (Finset.mem_univ a))
  have hBv : B *ᵥ v = μ • v := by
    rw [hv, Matrix.mulVec_mulVec, hBL, Matrix.smul_mulVec]
  -- `y(τ + t) = e^{Bt} z`
  have hsemi : ∀ t : ℝ, exp ((t + τ) • B) *ᵥ y₀ = exp (t • B) *ᵥ z := by
    intro t
    rw [hz, Matrix.mulVec_mulVec, ← exp_add_smul]
  -- `y(τ + t) / (t^k e^{μ t}) → v`
  have hcoord : ∀ a, Tendsto (fun t : ℝ => (exp (t • B) *ᵥ z) a / (t ^ k * Real.exp (μ * t)))
      atTop (𝓝 (v a)) := by
    intro a
    have h := tendsto_finsetSum Finset.univ fun b (_ : b ∈ Finset.univ) =>
      (hL a b).mul_const (z b)
    rw [hv]
    refine h.congr fun t => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hsumlim : Tendsto (fun t : ℝ => (∑ a, (exp (t • B) *ᵥ z) a) /
      (t ^ k * Real.exp (μ * t))) atTop (𝓝 (∑ a, v a)) := by
    have h := tendsto_finsetSum Finset.univ fun a (_ : a ∈ Finset.univ) => hcoord a
    refine h.congr fun t => ?_
    rw [Finset.sum_div]
  -- dividing the two limits
  have hquot : ∀ a, Tendsto (fun t : ℝ => (∑ i, (exp (t • B) *ᵥ z) i)⁻¹ *
      (exp (t • B) *ᵥ z) a) atTop (𝓝 (v a / ∑ i, v i)) := by
    intro a
    have h := (hcoord a).div hsumlim hvpos.ne'
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hD : t ^ k * Real.exp (μ * t) ≠ 0 := (mul_pos (pow_pos ht k) (Real.exp_pos _)).ne'
    rw [Pi.div_apply, div_div_div_cancel_right₀ hD, div_eq_inv_mul]
  refine ⟨fun a => v a / ∑ i, v i, fun a => div_nonneg (hv0 a) hvpos.le, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hvpos.ne']
  · have hq : (fun a => v a / ∑ i, v i) = (∑ i, v i)⁻¹ • v := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hq, Matrix.mulVec_smul, hBv, smul_comm]
  · -- shift time back by `τ`
    rw [tendsto_pi_nhds]
    intro a
    have h := (hquot a).comp (tendsto_atTop_add_const_right atTop (-τ) tendsto_id)
    refine h.congr fun t => ?_
    have ht : exp ((t + -τ) • B) *ᵥ z = exp (t • B) *ᵥ y₀ := by
      rw [← hsemi, neg_add_cancel_right]
    simp only [Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, ht]

end Reduced

/-! ## Step 2: only the reachable indices matter -/

section Full

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {x₀ : ι → ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- A nonnegative, nonzero vector has a positive entry: the support `S` is not empty. -/
theorem exists_pos_of_nonneg_of_ne_zero (hx₀ : ∀ i, 0 ≤ x₀ i) (hne : x₀ ≠ 0) : ∃ j, 0 < x₀ j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  exact ⟨j, lt_of_le_of_ne (hx₀ j) (Ne.symm hj)⟩

omit [DecidableEq ι] in
/-- A sum over the subtype of a finite set `R` is the full sum, for a function vanishing
outside `R`. -/
theorem sum_coe_eq_sum_of_eq_zero {R : Finset ι} {f : ι → ℝ} (hf : ∀ i ∉ R, f i = 0) :
    ∑ j : R, f j = ∑ i, f i := by
  rw [Finset.sum_coe_sort R f]
  exact Finset.sum_subset (Finset.subset_univ R) fun i _ hi => hf i hi

/-- If `M p = μ p` for a nonzero vector `p`, then `μ` is an eigenvalue of `M`. -/
theorem mem_spectrum_of_mulVec_eq_smul {μ : ℝ} {p : ι → ℝ} (hp : p ≠ 0) (h : M *ᵥ p = μ • p) :
    μ ∈ spectrum ℝ M := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hp⟩
  rw [Matrix.toLin'_apply]
  exact h

/-- The solution `e^{Mt} x₀` is nonnegative for `t ≥ 0`. -/
theorem exp_smul_mulVec_nonneg (hM : IsMetzler M) (hx₀ : ∀ i, 0 ≤ x₀ i) {t : ℝ} (ht : 0 ≤ t)
    (i : ι) : 0 ≤ (exp (t • M) *ᵥ x₀) i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (exp_smul_apply_nonneg hM ht i j) (hx₀ j)

/-- Step 2, equation (support): `xᵢ(t) > 0` for `t > 0` if `i ∈ R`. -/
theorem exp_smul_mulVec_pos (hM : IsMetzler M) (hx₀ : ∀ i, 0 ≤ x₀ i) {t : ℝ} (ht : 0 < t)
    {i : ι} (hi : i ∈ reachSet M x₀) : 0 < (exp (t • M) *ᵥ x₀) i := by
  obtain ⟨j, hj, hji⟩ := mem_reachSet.1 hi
  have hpos : 0 < (exp (t • M)) i j * x₀ j := mul_pos (exp_smul_apply_pos hM ht hji) hj
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (f := fun j => (exp (t • M)) i j * x₀ j)
      (fun j _ => mul_nonneg (exp_smul_apply_nonneg hM ht.le i j) (hx₀ j)) (Finset.mem_univ j))

/-- Step 2, equation (support): `xᵢ(t) = 0` if `i ∉ R`. -/
theorem exp_smul_mulVec_eq_zero (hM : IsMetzler M) (hx₀ : ∀ i, 0 ≤ x₀ i) (t : ℝ) {i : ι}
    (hi : i ∉ reachSet M x₀) : (exp (t • M) *ᵥ x₀) i = 0 := by
  change ∑ j, (exp (t • M)) i j * x₀ j = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : 0 < x₀ j
  · have hnr : ¬ Reachable M j i := fun h => hi (mem_reachSet.2 ⟨j, hj, h⟩)
    rw [exp_smul_apply_eq_zero hM t hnr, zero_mul]
  · have hzero : x₀ j = 0 := le_antisymm (not_lt.1 hj) (hx₀ j)
    rw [hzero, mul_zero]

/-- Step 2: the total `W(t) = ∑ᵢ xᵢ(t)` is positive for `t ≥ 0`. -/
theorem sum_exp_smul_mulVec_pos (hM : IsMetzler M) (hx₀ : ∀ i, 0 ≤ x₀ i) (hne : x₀ ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 < ∑ i, (exp (t • M) *ᵥ x₀) i := by
  obtain ⟨j, hj⟩ := exists_pos_of_nonneg_of_ne_zero hx₀ hne
  have hjpos : 0 < (exp (t • M) *ᵥ x₀) j := by
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, exp_zero_smul, Matrix.one_mulVec]
      exact hj
    · exact exp_smul_mulVec_pos hM hx₀ hpos (mem_reachSet_of_pos hj)
  exact lt_of_lt_of_le hjpos
    (Finset.single_le_sum (f := fun i => (exp (t • M) *ᵥ x₀) i)
      (fun i _ => exp_smul_mulVec_nonneg hM hx₀ ht i) (Finset.mem_univ j))

/-- Step 2, the reduced system: `y(t) = x_R(t)` satisfies `ẏ = B y`, hence `y(t) = e^{Bt} y(0)`,
where `B = M_RR`. -/
theorem restrict_exp_smul_mulVec (hM : IsMetzler M) (hx₀ : ∀ i, 0 ≤ x₀ i) {t : ℝ} (ht : 0 ≤ t)
    (i : reachSet M x₀) :
    (exp (t • M) *ᵥ x₀) i =
      (exp (t • reducedMatrix M x₀) *ᵥ fun j : reachSet M x₀ => x₀ j) i := by
  -- `ẏ = B y`, because `x_j ≡ 0` for `j ∉ R`
  have hy : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => fun i : reachSet M x₀ => (exp (s • M) *ᵥ x₀) i)
      (reducedMatrix M x₀ *ᵥ fun i : reachSet M x₀ => (exp (s • M) *ᵥ x₀) i) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h := hasDerivAt_pi.1 (hasDerivAt_exp_smul_mulVec M x₀ s) i
    have heq : (M *ᵥ (exp (s • M) *ᵥ x₀)) i =
        (reducedMatrix M x₀ *ᵥ fun j : reachSet M x₀ => (exp (s • M) *ᵥ x₀) j) i := by
      change ∑ j, M i j * (exp (s • M) *ᵥ x₀) j =
        ∑ j : reachSet M x₀, M i j * (exp (s • M) *ᵥ x₀) j
      exact (sum_coe_eq_sum_of_eq_zero (f := fun j => M i j * (exp (s • M) *ᵥ x₀) j)
        fun j hj => by rw [exp_smul_mulVec_eq_zero hM hx₀ s hj, mul_zero]).symm
    rw [heq] at h
    exact h
  have hsol : (fun i : reachSet M x₀ => (exp (t • M) *ᵥ x₀) i) =
      exp (t • reducedMatrix M x₀) *ᵥ
        (fun i : reachSet M x₀ => (exp ((0 : ℝ) • M) *ᵥ x₀) i) :=
    eq_exp_smul_mulVec_of_hasDerivWithinAt (reducedMatrix M x₀)
      (fun s : ℝ => fun i : reachSet M x₀ => (exp (s • M) *ᵥ x₀) i)
      (fun s _ => (hy s).hasDerivWithinAt) t ht
  have h0 : (fun i : reachSet M x₀ => (exp ((0 : ℝ) • M) *ᵥ x₀) i) =
      fun j : reachSet M x₀ => x₀ j := by
    funext i
    rw [exp_zero_smul, Matrix.one_mulVec]
  rw [h0] at hsol
  exact congrFun hsol i

end Full

/-! ## Theorem 2 -/

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 2** of the text.

Standing hypotheses: `M` is a real square matrix with nonnegative off-diagonal entries
(`IsMetzler M`); the initial state `x 0` is nonnegative and nonzero; and `x` solves `ẋ = M x` on
`[0, ∞)` (the derivative at `0` being one-sided).

Notation: `R = reachSet M (x 0)` is the set of indices reachable from the support of `x 0`, and
`B = reducedMatrix M (x 0)` is the principal submatrix `M_RR`. The total is `W(t) = ∑ᵢ xᵢ(t)` and
the vector of frequencies is `p(t) = W(t)⁻¹ • x(t)`.

Conclusions:

* (a) for every `t > 0`, `xᵢ(t) > 0` if `i ∈ R`; `xᵢ(t) = 0` for all `t ≥ 0` if `i ∉ R`; and
  `W(t) > 0` for all `t ≥ 0`;
* (b) there is a real number `μ` which is the largest real part of a (complex) eigenvalue of `B`
  and is itself an eigenvalue of `B`;
* (c) the limit `p* = lim_{t → ∞} p(t)` exists, and `p* ≥ 0`, `∑ᵢ p*ᵢ = 1`, `p*ᵢ = 0` for
  `i ∉ R`, and `M p* = μ p*`; in particular `μ` is an eigenvalue of `M`. -/
theorem tendsto_normalized_solution (M : Matrix ι ι ℝ) (hM : IsMetzler M) (x : ℝ → ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x 0 i) (hx0' : x 0 ≠ 0)
    (hx : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt x (M *ᵥ x t) (Set.Ici 0) t) :
    ((∀ t : ℝ, 0 < t → ∀ i ∈ reachSet M (x 0), 0 < x t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i ∉ reachSet M (x 0), x t i = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < ∑ i, x t i)) ∧
    ∃ μ : ℝ,
      (IsGreatest
          (Complex.re '' spectrum ℂ ((reducedMatrix M (x 0)).map (algebraMap ℝ ℂ))) μ ∧
        μ ∈ spectrum ℝ (reducedMatrix M (x 0))) ∧
      ∃ p : ι → ℝ,
        Tendsto (fun t : ℝ => (∑ i, x t i)⁻¹ • x t) atTop (nhds p) ∧
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i ∉ reachSet M (x 0), p i = 0) ∧
            M *ᵥ p = μ • p ∧ μ ∈ spectrum ℝ M := by
  -- Lemma 3 (a): the solution is `x(t) = e^{Mt} x(0)`
  have hsol : ∀ t : ℝ, 0 ≤ t → x t = exp (t • M) *ᵥ x 0 := fun t ht =>
    eq_exp_smul_mulVec_of_hasDerivWithinAt M x hx t ht
  refine ⟨⟨fun t ht i hi => ?_, fun t ht i hi => ?_, fun t ht => ?_⟩, ?_⟩
  -- part (a), by Step 2
  · rw [hsol t ht.le]
    exact exp_smul_mulVec_pos hM hx0 ht hi
  · rw [hsol t ht]
    exact exp_smul_mulVec_eq_zero hM hx0 t hi
  · rw [hsol t ht]
    exact sum_exp_smul_mulVec_pos hM hx0 hx0' ht
  -- parts (b) and (c)
  · obtain ⟨j₀, hj₀⟩ := exists_pos_of_nonneg_of_ne_zero hx0 hx0'
    have : Nonempty (reachSet M (x 0)) := ⟨⟨j₀, mem_reachSet_of_pos hj₀⟩⟩
    have hB : IsMetzler (reducedMatrix M (x 0)) := hM.reducedMatrix (x 0)
    -- Step 3: Lemma 5 for `B` gives `μ`, which proves part (b)
    obtain ⟨μ, hμ, hdom⟩ := exists_dominant_eigenvalue hB
    refine ⟨μ, ⟨isGreatest_re_spectrum hμ hdom, (ofReal_mem_spectrum_map_iff _ μ).1 hμ⟩, ?_⟩
    -- Step 2: the reduced system `y(t) = x_R(t) = e^{Bt} y(0)`, with `y(t) ≫ 0` for `t > 0`
    have hy : ∀ t : ℝ, 0 ≤ t → ∀ i : reachSet M (x 0), (exp (t • M) *ᵥ x 0) i =
        (exp (t • reducedMatrix M (x 0)) *ᵥ fun j : reachSet M (x 0) => x 0 j) i :=
      fun t ht i => restrict_exp_smul_mulVec hM hx0 ht i
    have hτ : ∀ i : reachSet M (x 0),
        0 < (exp ((1 : ℝ) • reducedMatrix M (x 0)) *ᵥ fun j : reachSet M (x 0) => x 0 j) i := by
      intro i
      rw [← hy 1 zero_le_one i]
      exact exp_smul_mulVec_pos hM hx0 zero_lt_one i.2
    -- Steps 3–5: the limit `q` for the reduced system
    obtain ⟨q, hq0, hq1, hBq, hqlim⟩ := tendsto_normalized_of_pos hB hμ hdom _ hτ
    -- Step 6: back to the full system; `p*` is `q` on `R` and `0` elsewhere
    have hpdef : ∀ i (h : i ∈ reachSet M (x 0)),
        (fun i => if h : i ∈ reachSet M (x 0) then q ⟨i, h⟩ else 0) i = q ⟨i, h⟩ := fun i h => by
      simp only [h, dite_true]
    have hpzero : ∀ i, i ∉ reachSet M (x 0) →
        (fun i => if h : i ∈ reachSet M (x 0) then q ⟨i, h⟩ else 0) i = 0 := fun i h => by
      simp only [h, dite_false]
    obtain ⟨p, hp⟩ : ∃ p : ι → ℝ,
        p = fun i => if h : i ∈ reachSet M (x 0) then q ⟨i, h⟩ else 0 := ⟨_, rfl⟩
    rw [← hp] at hpdef hpzero
    have hpcoe : ∀ j : reachSet M (x 0), p j = q j := fun j => hpdef j j.2
    -- `∑ p* = 1`
    have hpsum : ∑ i, p i = 1 := by
      rw [← sum_coe_eq_sum_of_eq_zero (R := reachSet M (x 0)) (f := p) hpzero, ← hq1]
      exact Finset.sum_congr rfl fun j _ => hpcoe j
    -- `M p* = μ p*`
    have hMp : M *ᵥ p = μ • p := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases hi : i ∈ reachSet M (x 0)
      · -- for `i ∈ R` this is `(B q)_i = μ q_i`
        have h1 : (M *ᵥ p) i = ∑ j : reachSet M (x 0), M i j * p j :=
          (sum_coe_eq_sum_of_eq_zero (R := reachSet M (x 0)) (f := fun j => M i j * p j)
            fun j hj => by rw [hpzero j hj, mul_zero]).symm
        have h2 : ∑ j : reachSet M (x 0), M i j * p j =
            (reducedMatrix M (x 0) *ᵥ q) ⟨i, hi⟩ :=
          Finset.sum_congr rfl fun j _ => by rw [hpcoe j]; rfl
        rw [h1, h2, hBq, Pi.smul_apply, smul_eq_mul, hpdef i hi]
      · -- for `i ∉ R` both sides vanish, by equation (noarc)
        rw [hpzero i hi, mul_zero]
        change ∑ j, M i j * p j = 0
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ∈ reachSet M (x 0)
        · rw [apply_eq_zero_of_mem_of_notMem hM hj hi, zero_mul]
        · rw [hpzero j hj, mul_zero]
    -- in particular `μ` is an eigenvalue of `M`, because `p* ≠ 0`
    have hpne : p ≠ 0 := by
      intro h
      rw [h] at hpsum
      simp at hpsum
    refine ⟨p, ?_, ?_, hpsum, hpzero, hMp, mem_spectrum_of_mulVec_eq_smul hpne hMp⟩
    · -- `p(t) → p*`
      rw [tendsto_pi_nhds]
      intro i
      by_cases hi : i ∈ reachSet M (x 0)
      · rw [hpdef i hi]
        have h := tendsto_pi_nhds.1 hqlim ⟨i, hi⟩
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        have hsum : ∑ j : reachSet M (x 0),
            (exp (t • reducedMatrix M (x 0)) *ᵥ fun j : reachSet M (x 0) => x 0 j) j =
            ∑ i, (exp (t • M) *ᵥ x 0) i := by
          rw [← sum_coe_eq_sum_of_eq_zero (R := reachSet M (x 0))
            (f := fun i => (exp (t • M) *ᵥ x 0) i)
            fun i hi => exp_smul_mulVec_eq_zero hM hx0 t hi]
          exact Finset.sum_congr rfl fun j _ => (hy t ht j).symm
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hsum, ← hy t ht ⟨i, hi⟩, hsol t ht]
      · rw [hpzero i hi]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hsol t ht, exp_smul_mulVec_eq_zero hM hx0 t hi, mul_zero]
    · -- `p* ≥ 0`
      intro i
      by_cases hi : i ∈ reachSet M (x 0)
      · rw [hpdef i hi]
        exact hq0 _
      · rw [hpzero i hi]

/-- Theorem 2 with the differential equation stated by two-sided derivatives: `x` has derivative
`M x(t)` at every `t ≥ 0`. This hypothesis is stronger than that of
`tendsto_normalized_solution`. -/
theorem tendsto_normalized_solution_of_hasDerivAt (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (x : ℝ → ι → ℝ) (hx0 : ∀ i, 0 ≤ x 0 i) (hx0' : x 0 ≠ 0)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (M *ᵥ x t) t) :
    ((∀ t : ℝ, 0 < t → ∀ i ∈ reachSet M (x 0), 0 < x t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i ∉ reachSet M (x 0), x t i = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < ∑ i, x t i)) ∧
    ∃ μ : ℝ,
      (IsGreatest
          (Complex.re '' spectrum ℂ ((reducedMatrix M (x 0)).map (algebraMap ℝ ℂ))) μ ∧
        μ ∈ spectrum ℝ (reducedMatrix M (x 0))) ∧
      ∃ p : ι → ℝ,
        Tendsto (fun t : ℝ => (∑ i, x t i)⁻¹ • x t) atTop (nhds p) ∧
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i ∉ reachSet M (x 0), p i = 0) ∧
            M *ᵥ p = μ • p ∧ μ ∈ spectrum ℝ M :=
  tendsto_normalized_solution M hM x hx0 hx0' fun t ht => (hx t ht).hasDerivWithinAt

/-- Theorem 2 under the weakest notion of solution: `x` is continuous on `[0, ∞)` and has
derivative `M x(t)` at every `t > 0`. (Such an `x` automatically has the one-sided derivative at
`0` that `tendsto_normalized_solution` asks for.) -/
theorem tendsto_normalized_solution_of_continuousOn (M : Matrix ι ι ℝ) (hM : IsMetzler M)
    (x : ℝ → ι → ℝ) (hx0 : ∀ i, 0 ≤ x 0 i) (hx0' : x 0 ≠ 0) (hc : ContinuousOn x (Set.Ici 0))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (M *ᵥ x t) t) :
    ((∀ t : ℝ, 0 < t → ∀ i ∈ reachSet M (x 0), 0 < x t i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i ∉ reachSet M (x 0), x t i = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < ∑ i, x t i)) ∧
    ∃ μ : ℝ,
      (IsGreatest
          (Complex.re '' spectrum ℂ ((reducedMatrix M (x 0)).map (algebraMap ℝ ℂ))) μ ∧
        μ ∈ spectrum ℝ (reducedMatrix M (x 0))) ∧
      ∃ p : ι → ℝ,
        Tendsto (fun t : ℝ => (∑ i, x t i)⁻¹ • x t) atTop (nhds p) ∧
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i ∉ reachSet M (x 0), p i = 0) ∧
            M *ᵥ p = μ • p ∧ μ ∈ spectrum ℝ M := by
  have hsol := eq_exp_smul_mulVec_of_continuousOn M x hc hx
  refine tendsto_normalized_solution M hM x hx0 hx0' fun t ht => ?_
  rcases (Set.mem_Ici.1 ht).eq_or_lt with h0 | hpos
  · -- at `t = 0`, `x` agrees on `[0, ∞)` with the differentiable function `e^{Mt} x(0)`
    subst h0
    have h := (hasDerivAt_exp_smul_mulVec M (x 0) 0).hasDerivWithinAt (s := Set.Ici 0)
    rw [exp_zero_smul, Matrix.one_mulVec] at h
    exact h.congr (fun s hs => hsol s hs) (hsol 0 (Set.mem_Ici.2 le_rfl))
  · exact (hx t hpos).hasDerivWithinAt

/-- Theorem 2 for the solution written out as `x(t) = e^{Mt} x₀`. In particular the hypotheses
of `tendsto_normalized_solution` can be met: for every Metzler matrix `M` and every nonnegative,
nonzero `x₀` the function `t ↦ e^{Mt} x₀` is a solution with initial state `x₀`. -/
theorem tendsto_normalized_solution_exp (M : Matrix ι ι ℝ) (hM : IsMetzler M) (x₀ : ι → ℝ)
    (hx₀ : ∀ i, 0 ≤ x₀ i) (hne : x₀ ≠ 0) :
    ((∀ t : ℝ, 0 < t → ∀ i ∈ reachSet M x₀, 0 < (exp (t • M) *ᵥ x₀) i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i ∉ reachSet M x₀, (exp (t • M) *ᵥ x₀) i = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < ∑ i, (exp (t • M) *ᵥ x₀) i)) ∧
    ∃ μ : ℝ,
      (IsGreatest
          (Complex.re '' spectrum ℂ ((reducedMatrix M x₀).map (algebraMap ℝ ℂ))) μ ∧
        μ ∈ spectrum ℝ (reducedMatrix M x₀)) ∧
      ∃ p : ι → ℝ,
        Tendsto (fun t : ℝ => (∑ i, (exp (t • M) *ᵥ x₀) i)⁻¹ • (exp (t • M) *ᵥ x₀)) atTop
            (nhds p) ∧
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i ∉ reachSet M x₀, p i = 0) ∧
            M *ᵥ p = μ • p ∧ μ ∈ spectrum ℝ M := by
  have h0 : exp ((0 : ℝ) • M) *ᵥ x₀ = x₀ := by
    rw [exp_zero_smul, Matrix.one_mulVec]
  have h := tendsto_normalized_solution M hM (fun t : ℝ => exp (t • M) *ᵥ x₀)
    (by simpa only [h0] using hx₀) (by simpa only [h0] using hne)
    (fun t _ => (hasDerivAt_exp_smul_mulVec M x₀ t).hasDerivWithinAt)
  rw [h0] at h
  exact h

end Main

end PosLinearSys
