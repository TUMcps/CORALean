import CORALean.Global.Partition
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.Plus

/-!
# Disjoint buckets merge independently

The multiple-bucket equation right after [1, Prop. 4]: refining
a bucket into two disjoint sub-buckets splits its box `W(·,B)·Y(B)` into the
Minkowski sum of the sub-buckets' own boxes. That is why several disjoint
buckets can be merged "in parallel" — the combined error either bucket
computation gives is the same one, so nothing about processing them together
versus one at a time has to be reconciled.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bucket-error box splits over a further split of its columns:
`eq:multiple-buckets` in [1], the combined bucket's error being the Minkowski
sum of the sub-buckets' errors. -/
theorem mergeError_split {m r r₁ r₂ : ℕ}
    (part : Split (Fin r) into (Fin r₁) and (Fin r₂))
    (M : Mat ℝ m r) (Y : Interval (Vec ℝ r)) :
    Interval.mtimes M Y
      = Interval.plus
          (Interval.mtimes (M.submatrix id part.left)
            ⟨Y.inf ∘ part.left, Y.sup ∘ part.left⟩)
          (Interval.mtimes (M.submatrix id part.right)
            ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩) := by -- --- PROOF ---
  -- an `Interval` has no proof field, so equal bounds are all `mergeError_split` needs
  have key : ∀ (I J : Interval (Vec ℝ m)), I.inf = J.inf → I.sup = J.sup → I = J := by
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
