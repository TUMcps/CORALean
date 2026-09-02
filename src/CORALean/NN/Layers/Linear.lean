import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.Layer

/-!
# The linear layer

CORA's `nnLinearLayer`: `x ↦ W x + b`. The only layer whose propagation is a set
operation and nothing else — `mtimes` for the weights, `plus` with the bias —
and so the only standard one that loses nothing at a representation closed under
both.

The bias enters as a box of zero width rather than through an operation of its
own, which is why `OfInterval` is asked for here and not a translation: a
representation that can absorb a box can absorb a point.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n m : ℕ}

def Layer.linear (W : Mat ℝ m n) (b : Vec ℝ m) : Layer S n m where
  eval x := W *ᵥ x + b
  propagate s := plus (mtimes W s) (ofInterval (Interval.point b))
  propagate_outer s _x hx :=
    plus_outer _ _ (Set.add_mem_add
      (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ (Interval.mem_point b)))

end CORALean.Real
