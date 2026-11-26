import PosLinearSysConvergence.Defs
import PosLinearSysConvergence.MatrixExp

/-!
# Step 1

`e^{Mt}` is nonnegative for a Metzler matrix `M`, and reachability decides which of its entries
are positive (equation (pattern) of the text):

* `exp_smul_apply_nonneg`: `[e^{Mt}]_{ij} ≥ 0` for `t ≥ 0`;
* `exp_smul_apply_pos`: `[e^{Mt}]_{ij} > 0` for `t > 0` if `i` is reachable from `j`;
* `exp_smul_apply_eq_zero`: `[e^{Mt}]_{ij} = 0` if `i` is not reachable from `j`.

As in the text, the proof writes `e^{Mt} = e^{-ct} ∑ₖ tᵏ/k! Pᵏ` with `P = M + cI ≥ 0`.
-/

namespace PosLinearSys

open Matrix NormedSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A constant `c ≥ 0` for which `M + cI` is entrywise nonnegative (when `M` is Metzler). The text
suggests `maxᵢ |Mᵢᵢ|`; the sum `∑ᵢ |Mᵢᵢ|` serves equally well. -/
noncomputable def shiftConst (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i, |M i i|

omit [DecidableEq ι] in
theorem shiftConst_nonneg (M : Matrix ι ι ℝ) : 0 ≤ shiftConst M :=
  Finset.sum_nonneg fun i _ => abs_nonneg (M i i)

/-- `P = M + cI` is entrywise nonnegative. -/
theorem add_shiftConst_apply_nonneg {M : Matrix ι ι ℝ} (hM : IsMetzler M) (i j : ι) :
    0 ≤ (M + shiftConst M • (1 : Matrix ι ι ℝ)) i j := by
  by_cases hij : i = j
  · subst hij
    have h1 : |M i i| ≤ shiftConst M :=
      Finset.single_le_sum (f := fun k => |M k k|) (fun k _ => abs_nonneg (M k k))
        (Finset.mem_univ i)
    have h2 := neg_abs_le (M i i)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linarith
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
      mul_zero, add_zero]
    exact hM i j hij

omit [Fintype ι] in
/-- `P = M + cI` and `M` have the same off-diagonal entries. -/
theorem add_smul_one_apply_of_ne (M : Matrix ι ι ℝ) (c : ℝ) {i j : ι} (hij : i ≠ j) :
    (M + c • (1 : Matrix ι ι ℝ)) i j = M i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
    mul_zero, add_zero]

/-- Every power of a nonnegative matrix is nonnegative. -/
theorem pow_apply_nonneg {P : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) (i j : ι) :
    0 ≤ (P ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hP l j)

/-- If `i` is reachable from `j`, then `[P^k]_{ij} > 0` for some `k`. -/
theorem exists_pow_apply_pos_of_reachable {M P : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPM : ∀ i j, i ≠ j → P i j = M i j) {i j : ι} (h : Reachable M j i) :
    ∃ k : ℕ, 0 < (P ^ k) i j := by
  unfold Reachable at h
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail a b _ hab ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    have hPba : 0 < P b a := by
      rw [hPM b a hab.1]
      exact hab.2
    have hpos : 0 < P b a * (P ^ k) a j := mul_pos hPba hk
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun l => P b l * (P ^ k) l j)
        (fun l _ => mul_nonneg (hP b l) (pow_apply_nonneg hP k l j)) (Finset.mem_univ a))

/-- If `[P^k]_{ij} ≠ 0` for some `k`, then `i` is reachable from `j`. -/
theorem reachable_of_pow_apply_ne_zero {M P : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPM : ∀ i j, i ≠ j → P i j = M i j) (k : ℕ) {i j : ι} (h : (P ^ k) i j ≠ 0) :
    Reachable M j i := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    by_cases hij : i = j
    · subst hij
      exact Reachable.refl M i
    · simp [hij] at h
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : P i l ≠ 0 := left_ne_zero_of_mul hl
    have h2 : (P ^ k) l j ≠ 0 := right_ne_zero_of_mul hl
    have hjl : Reachable M j l := ih h2
    by_cases hil : i = l
    · subst hil
      exact hjl
    · refine hjl.tail ⟨hil, ?_⟩
      rw [← hPM i l hil]
      exact lt_of_le_of_ne (hP i l) (Ne.symm h1)

/-- The power series of `e^{Pt}`, entry by entry. -/
theorem hasSum_exp_smul_apply (P : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹ * t ^ k) * (P ^ k) i j) ((exp (t • P)) i j) := by
  have hsum : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (t • P) ^ k) (exp (t • P)) := by
    open scoped Matrix.Norms.Operator in
    exact exp_series_hasSum_exp' (𝕂 := ℝ) (t • P)
  have h2 := hsum.map (Matrix.entryAddMonoidHom ℝ i j) (continuous_id.matrix_elem i j)
  have hfun : (⇑(Matrix.entryAddMonoidHom ℝ i j) ∘
      fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (t • P) ^ k) =
      fun k => ((k.factorial : ℝ)⁻¹ * t ^ k) * (P ^ k) i j := by
    funext k
    change (((k.factorial : ℝ)⁻¹) • (t • P) ^ k) i j = _
    rw [smul_pow, smul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [hfun] at h2
  exact h2

/-- `e^{Mt} = e^{-ct} e^{(M + cI)t}` (Lemma 3 (c)). -/
theorem exp_smul_eq_shift (M : Matrix ι ι ℝ) (c t : ℝ) :
    exp (t • M) = Real.exp (-c * t) • exp (t • (M + c • (1 : Matrix ι ι ℝ))) := by
  have h := exp_smul_add_smul_one (M + c • (1 : Matrix ι ι ℝ)) (-c) t
  rwa [neg_smul, add_neg_cancel_right] at h

section Metzler

variable {M : Matrix ι ι ℝ}

/-- Step 1: `e^{Mt} ≥ 0` for `t ≥ 0`. (This is also part (i) of the proof of Lemma 5.) -/
theorem exp_smul_apply_nonneg (hM : IsMetzler M) {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    0 ≤ (exp (t • M)) i j := by
  rw [exp_smul_eq_shift M (shiftConst M) t, Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg (Real.exp_pos _).le ?_
  refine HasSum.nonneg (fun k => ?_) (hasSum_exp_smul_apply _ t i j)
  exact mul_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (pow_nonneg ht k))
    (pow_apply_nonneg (add_shiftConst_apply_nonneg hM) k i j)

/-- Step 1, equation (pattern): for `t > 0`, `[e^{Mt}]_{ij} > 0` if `i` is reachable from `j`. -/
theorem exp_smul_apply_pos (hM : IsMetzler M) {t : ℝ} (ht : 0 < t) {i j : ι}
    (h : Reachable M j i) : 0 < (exp (t • M)) i j := by
  rw [exp_smul_eq_shift M (shiftConst M) t, Matrix.smul_apply, smul_eq_mul]
  refine mul_pos (Real.exp_pos _) ?_
  have hP := add_shiftConst_apply_nonneg hM
  obtain ⟨k, hk⟩ := exists_pow_apply_pos_of_reachable hP
    (fun i j hij => add_smul_one_apply_of_ne M (shiftConst M) hij) h
  have hterm : ∀ l : ℕ, 0 ≤ ((l.factorial : ℝ)⁻¹ * t ^ l) *
      ((M + shiftConst M • (1 : Matrix ι ι ℝ)) ^ l) i j := fun l =>
    mul_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (pow_nonneg ht.le l))
      (pow_apply_nonneg hP l i j)
  have hkpos : 0 < ((k.factorial : ℝ)⁻¹ * t ^ k) *
      ((M + shiftConst M • (1 : Matrix ι ι ℝ)) ^ k) i j :=
    mul_pos (mul_pos (inv_pos.2 (Nat.cast_pos.2 (Nat.factorial_pos k))) (pow_pos ht k)) hk
  exact lt_of_lt_of_le hkpos
    (le_hasSum (hasSum_exp_smul_apply _ t i j) k fun l _ => hterm l)

/-- Step 1, equation (pattern): `[e^{Mt}]_{ij} = 0` if `i` is not reachable from `j`. (This holds
for every real `t`.) -/
theorem exp_smul_apply_eq_zero (hM : IsMetzler M) (t : ℝ) {i j : ι} (h : ¬ Reachable M j i) :
    (exp (t • M)) i j = 0 := by
  rw [exp_smul_eq_shift M (shiftConst M) t, Matrix.smul_apply, smul_eq_mul]
  have hP := add_shiftConst_apply_nonneg hM
  have hzero : ∀ k : ℕ, ((M + shiftConst M • (1 : Matrix ι ι ℝ)) ^ k) i j = 0 := by
    intro k
    by_contra hne
    exact h (reachable_of_pow_apply_ne_zero hP
      (fun i j hij => add_smul_one_apply_of_ne M (shiftConst M) hij) k hne)
  have hsum := hasSum_exp_smul_apply (M + shiftConst M • (1 : Matrix ι ι ℝ)) t i j
  simp only [hzero, mul_zero] at hsum
  rw [hsum.unique hasSum_zero, mul_zero]

/-- Step 1, equation (pattern), as an equivalence: for `t > 0`, `[e^{Mt}]_{ij} > 0` exactly when
`i` is reachable from `j`. -/
theorem exp_smul_apply_pos_iff (hM : IsMetzler M) {t : ℝ} (ht : 0 < t) {i j : ι} :
    0 < (exp (t • M)) i j ↔ Reachable M j i := by
  refine ⟨fun h => ?_, exp_smul_apply_pos hM ht⟩
  by_contra hne
  rw [exp_smul_apply_eq_zero hM t hne] at h
  exact lt_irrefl 0 h

end Metzler

end PosLinearSys
