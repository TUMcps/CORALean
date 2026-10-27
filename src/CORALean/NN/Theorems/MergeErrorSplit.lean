module

public import CORALean.Global.Partition
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# Disjoint buckets merge independently

The multiple-bucket equation [1, Eq. (4)], right after Prop. 4: refining a
bucket into two disjoint sub-buckets splits its box `W(·,B)·Y(B)` into the
Minkowski sum of the sub-buckets' own boxes. That is why several disjoint
buckets can be merged "in parallel" — the combined error either bucket
computation gives is the same one, so nothing about processing them together
versus one at a time has to be reconciled.

## Inputs
* `m` – output width
* `r` – number of merged neurons
* `r₁` – size of the first sub-bucket
* `r₂` – size of the second sub-bucket
* `part` – split of the bucket into two sub-buckets
* `M` – weight matrix
* `Y` – bounds of the merged neurons

## Hypotheses
* none

## Conclusion
* the bucket's error box is the sum of the sub-buckets' error boxes

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bucket-error box splits over a further split of its columns:
[1, Eq. (4)], the combined bucket's error being the Minkowski sum of the
sub-buckets' errors. -/
theorem mergeError_split {m r r₁ r₂ : ℕ}
    (part : Split (Fin r) into (Fin r₁) ⊕ (Fin r₂))
    (M : Mat ℝ m r) (Y : Real.Interval (Vec ℝ r)) : -- --- CONCL ---
    Real.Interval.mtimes M Y
      = Real.Interval.plus
          (Real.Interval.mtimes (M.submatrix id part.left)
            ⟨Y.inf ∘ part.left, Y.sup ∘ part.left⟩)
          (Real.Interval.mtimes (M.submatrix id part.right)
            ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩) := by -- --- PROOF ---
  -- a `Real.Interval` has no proof field, so equal bounds are all `mergeError_split` needs
  have key : ∀ (I J : Real.Interval (Vec ℝ m)), I.inf = J.inf → I.sup = J.sup → I = J := by
    rintro ⟨i₁, s₁⟩ ⟨i₂, s₂⟩ rfl rfl
    rfl
  apply key
  · funext i
    -- the lower bound is a sum of `min` terms, and `sum_split₂` reads it off along `part`
    show (∑ k, min (M i k * Y.inf k) (M i k * Y.sup k))
        = (∑ l, min (M i (part.left l) * Y.inf (part.left l))
              (M i (part.left l) * Y.sup (part.left l)))
          + ∑ l, min (M i (part.right l) * Y.inf (part.right l))
              (M i (part.right l) * Y.sup (part.right l))
    exact part.sum_split₂ (fun k => min (M i k * Y.inf k) (M i k * Y.sup k))
  · funext i
    -- the same argument on the upper bound, `max` in place of `min`
    show (∑ k, max (M i k * Y.inf k) (M i k * Y.sup k))
        = (∑ l, max (M i (part.left l) * Y.inf (part.left l))
              (M i (part.left l) * Y.sup (part.left l)))
          + ∑ l, max (M i (part.right l) * Y.inf (part.right l))
              (M i (part.right l) * Y.sup (part.right l))
    exact part.sum_split₂ (fun k => max (M i k * Y.inf k) (M i k * Y.sup k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
