import CORALean.NN.Layer

/-!
# A layer at every level of precision

What abstraction refinement operates on [1]: one function, and an enclosure of
it for every order pattern. `Layer`'s obligation is asked at each pattern, so
every one is sound and a pattern is spent on precision alone — a polynomial
order, a sample count, a partition — never on correctness.

`eval` sits outside `enclose` rather than inside a family of `Layer`s, and
that placement is the invariant: a refinement may not change what the layer
computes, or the exact set the enclosures are enclosures *of* would move with
the schedule and nothing could be said about the limit.

A pattern carries a level per input neuron [1, Eq. 23], so a rule may spend an
order on one neuron and leave its neighbours alone. What a layer reads out of it
is the layer's business: `ActivationPolyRefine` takes an entry as an order
together with a range, and `Layer.refinable` reads nothing at all.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- The order pattern of one layer [1, Eq. 23]: the level each of its `n` input
neurons is abstracted at. A uniform level is `Function.const _ o`. -/
abbrev OrderPattern (n : ℕ) := Fin n → ℕ

structure RefinableLayer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  eval : Vec ℝ n → Vec ℝ m
  enclose : OrderPattern n → S n → S m
  enclose_outer (t : OrderPattern n) (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    eval x ∈ construct (enclose t s)

/-- The layer a pattern names, which is the only thing a network ever runs. -/
def RefinableLayer.atPattern (L : RefinableLayer S n m) (t : OrderPattern n) : Layer S n m where
  eval := L.eval
  enclose := L.enclose t
  enclose_outer := L.enclose_outer t


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A layer with nothing to spend: every pattern is the layer itself, which is
how a linear layer sits in a refinable network. -/
def Layer.refinable (L : Layer S n m) : RefinableLayer S n m where
  eval := L.eval
  enclose _ := L.enclose
  enclose_outer _ := L.enclose_outer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
