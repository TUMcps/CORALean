module

public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.NN.Definitions.IsInMergeBucket
public import CORALean.NN.Theorems.Real.MergeBucketWidth
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# What the tolerance buys

`neuronMerging_sandwich_outer` is sound at *every* bucket of [1]'s `B_{k,y,δ}`, so which `y` and `δ`
get chosen owes no proof. This is the statement that makes an automatic choice meaningful anyway:
the error the merge costs is linear in `δ`, so driving `δ` down drives the reduction's cost to zero.
`IsInMergeBucket` alone only bounds `Y.sup i - Y.inf i`, one-sided; a bucket with crossed bounds at
some index (denoting `∅`) satisfies that bound in the wrong direction, and the error box's *width*
needs the other side too. `hY : Y.IsNonempty` is the one hypothesis this adds to the plan, exactly
what a real relaxation's output box always has.

## Inputs
* `n` – layer width
* `n₂` – output width
* `Y` – bounds of the layer's neurons
* `y` – merge value
* `δ` – merge tolerance
* `W` – weight matrix
* `i` – output index

## Hypotheses
* `hδ` – tolerance is nonnegative
* `hY` – the bounds are nonempty

## Conclusion
* the error box is at most twice the tolerance wide per unit of the bucket's row weight

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
section
variable {n m : ℕ}

/-- `Interval.mtimes`'s width, row by row. -/
theorem Interval.aux_mtimes_width (M : Mat ℝ m n) (I : Interval (Vec ℝ n))
    (i : Fin m) : -- --- CONCL ---
    (Interval.mtimes M I).sup i - (Interval.mtimes M I).inf i
      = ∑ k, |M i k| * |I.sup k - I.inf k| := by -- --- PROOF ---
  show (∑ k, max (M i k * I.inf k) (M i k * I.sup k))
      - ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
      = ∑ k, |M i k| * |I.sup k - I.inf k|
  rw [← Finset.sum_sub_distrib]
  -- each summand is `max - min` of the two endpoint products, an absolute difference
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [max_sub_min_eq_abs, ← mul_sub, abs_mul]

end
end Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bucket-error box `EB` `neuronMerging_sandwich_outer` adds is no wider than `2δ` per unit
of `W`'s row: driving the tolerance to `0` drives the merge's cost to `0`. -/
theorem mergeError_width_le {n n₂ : ℕ} (Y : Real.Interval (Vec ℝ n)) (y δ : ℝ) (hδ : 0 ≤ δ)
    (hY : Y.IsNonempty) (W : Mat ℝ n₂ n) (i : Fin n₂) : -- --- CONCL ---
    let EB := Real.Interval.mtimes (W.submatrix id (mergeSplit Y y δ).right)
      ⟨Y.inf ∘ (mergeSplit Y y δ).right, Y.sup ∘ (mergeSplit Y y δ).right⟩
    EB.sup i - EB.inf i ≤ (∑ k, |W i ((mergeSplit Y y δ).right k)|) * (2 * δ) := by -- --- PROOF ---
  intro EB
  rw [show EB = _ from rfl, Real.Interval.aux_mtimes_width, Finset.sum_mul]
  -- each column's width is at most `2δ`, its index lying in the bucket
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hbucket : IsInMergeBucket Y y δ ((mergeSplit Y y δ).right k) :=
    Partition.ofPred_right (IsInMergeBucket Y y δ) k
  have hwidth := mergeBucket_width Y y δ hbucket
  -- the bucket's own bounds are in order too, which is the other half `IsInMergeBucket` lacks
  have hnon : Y.inf ((mergeSplit Y y δ).right k) ≤ Y.sup ((mergeSplit Y y δ).right k) :=
    hY ((mergeSplit Y y δ).right k)
  show |Y.sup ((mergeSplit Y y δ).right k) - Y.inf ((mergeSplit Y y δ).right k)| ≤ 2 * δ
  exact abs_le.mpr ⟨by linarith, hwidth⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
