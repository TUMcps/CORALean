import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.Partition

/-!
# Merge buckets

[1, Def. 3]'s `B_{k,y,δ}`: the neurons of a nonlinear layer `k` whose bounds `Y`
fit inside `[y-δ, y+δ]`, so replacing all of them by the single value `y` costs
each at most `δ`. `mergeSplit` is the `Partition.ofPred` bridge into the split
`neuronMerging_sandwich_outer` consumes, survivors on the left.

No hypothesis `0 ≤ δ` appears anywhere below: at a negative `δ` the bucket is
merely empty, `mergeBucket_width` holding of it vacuously, so imposing one would
narrow every statement here for nothing.

`mergeRowWeight` sums a row of `W`, in absolute value, over *every* neuron
rather than over a bucket, since [1]'s tolerance search must pick `δ` before
any bucket exists to sum over.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]'s `B_{k,y,δ}`: the neurons whose bounds fit in `[y-δ, y+δ]`. -/
def mergeBucket {n : ℕ} (Y : Interval (Vec ℝ n)) (y δ : ℝ) (i : Fin n) : Prop :=
  y - δ ≤ Y.inf i ∧ Y.sup i ≤ y + δ

noncomputable instance {n : ℕ} (Y : Interval (Vec ℝ n)) (y δ : ℝ) :
    DecidablePred (mergeBucket Y y δ) :=
  fun i => by unfold mergeBucket; infer_instance

/-- The split `neuronMerging_sandwich_outer` consumes, survivors on the left. -/
noncomputable def mergeSplit {n : ℕ} (Y : Interval (Vec ℝ n)) (y δ : ℝ) :=
  Partition.ofPred (mergeBucket Y y δ)

/-- A bucketed neuron's bounds are within `2δ` of each other, `y ± δ` both between them. -/
theorem mergeBucket_width {n : ℕ} (Y : Interval (Vec ℝ n)) (y δ : ℝ) {i : Fin n}
    (hi : mergeBucket Y y δ i) : Y.sup i - Y.inf i ≤ 2 * δ := by
  linarith [hi.1, hi.2]

/-- The factor the merge's cost scales by at output `i`: `W`'s row, in absolute
value, over *all* neurons rather than over a bucket not yet chosen. -/
def mergeRowWeight {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) : ℝ := ∑ k, |W i k|

theorem mergeRowWeight_nonneg {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) :
    0 ≤ mergeRowWeight W i :=
  Finset.sum_nonneg fun k _ => abs_nonneg (W i k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
