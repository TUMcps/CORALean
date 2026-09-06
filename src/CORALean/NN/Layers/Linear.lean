import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
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

`Layer.linearWithError` is CORA's adaptation `W h + b ⊕ E` for a network already
carrying an approximation error. `E` need not be centred at `0` — a
neuron-merging error rarely is — so the layer commits to `E`'s own centre as its
nominal value and pays the rest into `propagate`, the way `Layer.activation`
pays a relaxation's error; `E.IsNonempty` is what puts that centre inside `E`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
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

/-- `Layer.linear` with an added error box `E`, CORA's `W h + b ⊕ E`. -/
noncomputable def Layer.linearWithError (W : Mat ℝ m n) (b : Vec ℝ m) (E : Interval (Vec ℝ m))
    (hE : E.IsNonempty) : Layer S n m where
  eval x := W *ᵥ x + b + E.center
  propagate s := plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E))
  propagate_outer s x hx := by
    -- the committed value is `E`'s own centre, which `mem_center` puts inside `E`
    have hbox : b + E.center ∈ construct (Interval.plus (Interval.point b) E) :=
      Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b)
        (Interval.mem_center E hE))
    show W *ᵥ x + b + E.center ∈ construct
        (plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E)))
    rw [add_assoc]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hbox))

end CORALean.Real
