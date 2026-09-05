import CORALean.NN.Layer

/-!
# A layer at every level of precision

What abstraction refinement operates on [1]: one function, and an enclosure of
it for every refinement level. `Layer`'s obligation is asked at each level, so
every level is sound and the level is spent on precision alone — a polynomial
order, a sample count, a partition — never on correctness.

`eval` sits outside `propagate` rather than inside a family of `Layer`s, and
that placement is the invariant: a refinement may not change what the layer
computes, or the exact set the enclosures are enclosures *of* would move with
the schedule and nothing could be said about the limit.

The level is a `ℕ` and what a layer does with it is the layer's business.
`ActivationPolyRefine` reads it as an order together with a range; a layer with
nothing to spend ignores it, which is `Layer.refinable`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

structure RefinableLayer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  eval : Vec ℝ n → Vec ℝ m
  propagate : ℕ → S n → S m
  propagate_outer (o : ℕ) (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    eval x ∈ construct (propagate o s)

/-- The layer a level names, which is the only thing a network ever runs. -/
def RefinableLayer.atLevel (L : RefinableLayer S n m) (o : ℕ) : Layer S n m where
  eval := L.eval
  propagate := L.propagate o
  propagate_outer := L.propagate_outer o

/-- A layer with nothing to spend: every level is the layer itself, which is how
a linear layer sits in a refinable network. -/
def Layer.refinable (L : Layer S n m) : RefinableLayer S n m where
  eval := L.eval
  propagate _ := L.propagate
  propagate_outer _ := L.propagate_outer

end CORALean.Real
