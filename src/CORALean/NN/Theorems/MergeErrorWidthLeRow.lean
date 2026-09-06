import CORALean.NN.Theorems.MergeErrorWidthLe

/-!
# The tolerance's cost, without knowing the bucket first

`mergeError_width_le` bounds a bucket's error box by *its own* row weight — the
sum of `|W i ·|` over the bucket's indices, known only once the bucket is
chosen. A tolerance search runs the other way, picking `δ` before any bucket
exists, so it needs a bound over every neuron instead: `mergeRowWeight`.

The bucket's part of a row is at most the whole row, both being sums of
absolute values over `Partition.sum_split₂` — [1]'s search cannot need a
sharper bound than this, since it cannot see the bucket yet either. That is
exactly what `exists_mergeTolerance` turns into an existence statement.

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

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mergeError_width_le`, coarsened to `mergeRowWeight`: the bound no longer
mentions the split at all, which is the point — it holds before `δ` picks any
bucket. -/
theorem mergeError_width_le_row {n n₂ : ℕ} (Y : Interval (Vec ℝ n)) (y δ : ℝ) (hδ : 0 ≤ δ)
    (hY : Y.IsNonempty) (W : Mat ℝ n₂ n) (i : Fin n₂) :
    let EB := Interval.mtimes (W.submatrix id (mergeSplit Y y δ).right)
      ⟨Y.inf ∘ (mergeSplit Y y δ).right, Y.sup ∘ (mergeSplit Y y δ).right⟩
    EB.sup i - EB.inf i ≤ mergeRowWeight W i * (2 * δ) := by -- --- PROOF ---
  intro EB
  have hbase := mergeError_width_le Y y δ hδ hY W i
  have hsplit := (mergeSplit Y y δ).sum_split₂ (fun k => |W i k|)
  have hleft_nonneg : (0:ℝ) ≤ ∑ l, |W i ((mergeSplit Y y δ).left l)| :=
    Finset.sum_nonneg fun l _ => abs_nonneg _
  -- the bucket's part of the row is at most the whole row, the survivors' part being nonnegative
  have hbucket_le : (∑ k, |W i ((mergeSplit Y y δ).right k)|) ≤ mergeRowWeight W i := by
    show (∑ k, |W i ((mergeSplit Y y δ).right k)|) ≤ ∑ k, |W i k|
    linarith
  exact le_trans hbase (mul_le_mul_of_nonneg_right hbucket_le (by linarith))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
