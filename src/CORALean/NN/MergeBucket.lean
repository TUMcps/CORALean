import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.Partition

/-!
# Merge buckets

[1]'s `B_{k,y,δ}`: the neurons of a nonlinear layer `k` whose output bounds `Y`
fit inside `[y-δ, y+δ]`, so replacing all of them by the single value `y` costs
each at most `δ`. `mergeSplit` is the `Partition.ofPred` bridge into the split
`neuronMerging_sandwich_outer` consumes, survivors on the left.

No hypothesis `0 ≤ δ` appears anywhere below: at a negative `δ` the bucket is
merely empty, `mergeBucket_width` holding of it vacuously, so imposing one would
narrow every statement here for nothing.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `B_{k,y,δ}`: the neurons whose output bounds fit inside `[y-δ, y+δ]`. -/
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
