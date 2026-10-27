module

public import CORALean.ContSet.Interval.Float.Operations.ExactSquare
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Theorems.ExactSquareOuter

@[expose] public section

/-!
# `Interval.exactSquare` contains the squares of the members

Every product of entries is bracketed by the corner hull of its factors' intervals, the sum `A i i
+ A j j` by the directed sums of the ends, the square of a diagonal entry by `aux_squareLo` and
`aux_squareHi`, and the sums over `k` by `sumDown` and `sumUp`; the sum over the indices other
than `i` and `j` is the full sum less the two split-off terms, as in the exact layer.

## Inputs
* `A` – interval matrix
* `M` – member matrix

## Hypotheses
* `hM` – `M` lies in the interval matrix

## Conclusion
* `M * M` lies in `exactSquare`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every square of a point of `[a, b]` lies between the two directed bounds. -/
private theorem Interval.aux_square_between {a b : 𝕋} {x : ℝ} (h₁ : toReal a ≤ x)
    (h₂ : x ≤ toReal b) : -- --- CONCL ---
    toReal (Interval.aux_squareLo a b) ≤ x ^ 2 ∧
      x ^ 2 ≤ toReal (Interval.aux_squareHi a b) := by -- --- PROOF ---
  constructor
  · unfold Interval.aux_squareLo
    split
    · rename_i h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · -- `0 ≤ a`: the smaller square is that of `a`
        have h0 := toReal_le_of_le h
        rw [toReal_zero] at h0
        rw [toReal_minimum]
        exact le_trans (min_le_left _ _) (le_trans (mulDown_le_mul a a) (by nlinarith))
      · -- `b ≤ 0`: that of `b`
        have h0 := toReal_le_of_le h
        rw [toReal_zero] at h0
        rw [toReal_minimum]
        exact le_trans (min_le_right _ _) (le_trans (mulDown_le_mul b b) (by nlinarith))
    · rw [toReal_zero]; exact sq_nonneg x
  · unfold Interval.aux_squareHi
    rw [toReal_maximum]
    have ha := mul_le_mulUp a a
    have hb := mul_le_mulUp b b
    -- the point is nonnegative and below `b`, or negative and above `a`
    rcases le_total 0 x with hx | hx
    · exact le_trans (by nlinarith) (le_trans hb (le_max_right _ _))
    · exact le_trans (by nlinarith) (le_trans ha (le_max_left _ _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exactSquare_outer (A : Interval (Mat 𝕋 n n)) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) : -- --- CONCL ---
    M * M ∈ A.exactSquare.construct := by -- --- PROOF ---
  have hm := Interval.mem_mat_iff.mp hM
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · -- the diagonal: the square of `M i i` and the `k ≠ i` products
    subst hij
    simp only [Interval.exactSquare, if_true]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hs := fun k (_ : k ∈ Finset.univ.erase i) =>
      Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k i).1 (hm k i).2
    -- the sums over all `k` with the split-off term replaced by `0` are the sums over `k ≠ i`
    have hlo : ∑ k, toReal (if k = i then (zero : 𝕋) else Interval.mulLo (A.inf i k) (A.sup i k)
        (A.inf k i) (A.sup k i)) ≤ ∑ k ∈ Finset.univ.erase i, M i k * M k i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos (rfl : i = i), toReal_zero,
        zero_add]
      exact Finset.sum_le_sum fun k hk => by
        rw [if_neg (Finset.ne_of_mem_erase hk)]; exact (hs k hk).1
    have hhi : ∑ k ∈ Finset.univ.erase i, M i k * M k i ≤ ∑ k, toReal (if k = i then (zero : 𝕋)
        else Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos (rfl : i = i), toReal_zero,
        zero_add]
      exact Finset.sum_le_sum fun k hk => by
        rw [if_neg (Finset.ne_of_mem_erase hk)]; exact (hs k hk).2
    have hsq := Interval.aux_square_between (hm i i).1 (hm i i).2
    rw [sq] at hsq
    exact ⟨le_trans (addDown_le_add _ _) (add_le_add hsq.1 (le_trans (sumDown_le_sum _) hlo)),
      le_trans (add_le_add hsq.2 (le_trans hhi (sum_le_sumUp _))) (add_le_addUp _ _)⟩
  · -- off the diagonal: split at `k = i` and `k = j`
    simp only [Interval.exactSquare, hij, if_false]
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ hj]
    have hd : (Finset.univ.erase i).erase j = Finset.univ \ {i, j} := by
      ext k; simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    rw [hd]
    have hm' := Interval.mul_between_corners (hm i j).1 (hm i j).2
      (le_trans (addDown_le_add (A.inf i i) (A.inf j j)) (add_le_add (hm i i).1 (hm j j).1))
      (le_trans (add_le_add (hm i i).2 (hm j j).2) (add_le_addUp (A.sup i i) (A.sup j j)))
    have hs := fun k (_ : k ∈ Finset.univ \ {i, j}) =>
      Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2
    -- the sums over all `k` with the two split-off terms replaced by `0` are the sums over the rest
    have hzero : ∀ f : Fin n → 𝕋, ∑ k, toReal (if k = i ∨ k = j then (zero : 𝕋) else f k)
        = ∑ k ∈ Finset.univ \ {i, j}, toReal (f k) := by
      intro f
      rw [← Finset.sum_sdiff (Finset.subset_univ {i, j})]
      have h0 : ∑ k ∈ ({i, j} : Finset (Fin n)), toReal (if k = i ∨ k = j then (zero : 𝕋)
          else f k) = 0 := Finset.sum_eq_zero fun k hk => by
        rw [if_pos (by simpa using hk), toReal_zero]
      rw [h0, add_zero]
      exact Finset.sum_congr rfl fun k hk => by
        rw [if_neg (by simpa using hk)]
    have e : M i i * M i j + (M i j * M j j + ∑ k ∈ Finset.univ \ {i, j}, M i k * M k j)
        = M i j * (M i i + M j j) + ∑ k ∈ Finset.univ \ {i, j}, M i k * M k j := by ring
    rw [e]
    refine ⟨le_trans (addDown_le_add _ _) (add_le_add hm'.1 (le_trans (sumDown_le_sum _) ?_)),
      le_trans (add_le_add hm'.2 (le_trans ?_ (sum_le_sumUp _))) (add_le_addUp _ _)⟩
    · rw [hzero (fun k => Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j))]
      exact Finset.sum_le_sum fun k hk => (hs k hk).1
    · rw [hzero (fun k => Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j))]
      exact Finset.sum_le_sum fun k hk => (hs k hk).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
