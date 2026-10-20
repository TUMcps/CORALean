module

public import CORALean.ContSet.Interval.Real.Operations.ExactSquare
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.PowerBetween
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Interval.exactSquare` encloses every square of a matrix in the box

Entry `(i, j)` of `M * M` is split at `k = i, j`: off the diagonal the two terms through `M i j`
combine to `M i j * (M i i + M j j)`, bounded by the corner products against the sum of the two
diagonal intervals, and the rest term by term; on the diagonal `M i i * M i i` is the interval
power `pow_between`. The enclosure is entrywise, never a set equality
(`Theorems/ExactSquareEntryExact`).

## Inputs
* `A` – interval matrix
* `M` – member of the box

## Hypotheses
* `hM` – `M` lies in `A`

## Conclusion
* the square of `M` lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every square of a member of the box lies in `exactSquare`. -/
theorem Interval.exactSquare_outer (A : Interval (Mat ℝ n n)) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) : M * M ∈ A.exactSquare.construct := by -- --- PROOF ---
  have hm := Interval.mem_mat_iff.mp hM
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  simp only [Interval.exactSquare]
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · -- the diagonal: the square of `M i i` and the `k ≠ i` products
    subst hij
    simp only [if_true]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hp := Interval.pow_between 2 (hm i i).1 (hm i i).2
    simp only [Nat.reduceMod, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      true_and] at hp
    have hs := fun k (_ : k ∈ Finset.univ.erase i) =>
      Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k i).1 (hm k i).2
    refine ⟨add_le_add (by rw [← sq]; exact hp.1) (Finset.sum_le_sum fun k hk => (hs k hk).1),
      add_le_add (by rw [← sq]; exact hp.2) (Finset.sum_le_sum fun k hk => (hs k hk).2)⟩
  · -- off the diagonal: split at `k = i` and `k = j`
    simp only [hij, if_false]
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ hj]
    -- the remaining indices
    have hd : (Finset.univ.erase i).erase j = Finset.univ \ {i, j} := by
      ext k; simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    rw [hd]
    have hm' := Interval.mul_between_corners (hm i j).1 (hm i j).2
      (add_le_add (hm i i).1 (hm j j).1) (add_le_add (hm i i).2 (hm j j).2)
    have hs := fun k (_ : k ∈ Finset.univ \ {i, j}) =>
      Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2
    have e : M i i * M i j + (M i j * M j j + ∑ k ∈ Finset.univ \ {i, j}, M i k * M k j)
        = M i j * (M i i + M j j) + ∑ k ∈ Finset.univ \ {i, j}, M i k * M k j := by ring
    rw [e]
    exact ⟨add_le_add hm'.1 (Finset.sum_le_sum fun k hk => (hs k hk).1),
      add_le_add hm'.2 (Finset.sum_le_sum fun k hk => (hs k hk).2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
