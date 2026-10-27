module

public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# A layer at every level of precision

What abstraction refinement operates on [1]: one function, and an enclosure of it for every order
pattern. `Layer`'s obligation is asked at each pattern, so a pattern is spent on precision alone,
never on correctness. `eval` sits outside `enclose`: a refinement may not change what the layer
computes, or the exact set the enclosures are enclosures *of* would move with the schedule. It is a
specification and never a computation. A pattern carries a level per input neuron [1, Eq. 23]; what
a layer reads out of it is the layer's business: `ActivationPolyRefinable` takes an entry as an
order with a range, `Layer.refinable` reads nothing.

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- The order pattern of one layer [1, Eq. 23]: the level each of its `n` input
neurons is abstracted at. A uniform level is `Function.const _ o`. -/
abbrev OrderPattern (n : ℕ) := Fin n → ℕ


-- ========================================  MAIN TYPE  ========================================= --

/-- A layer with its exact function and, for every order pattern, an enclosure of its image of a
set. -/
structure RefinableLayer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  eval : Vec ℝ n → Vec ℝ m
  enclose : OrderPattern n → S n → S m
  enclose_outer (t : OrderPattern n) (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    eval x ∈ construct (enclose t s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
