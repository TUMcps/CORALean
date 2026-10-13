module

public import CORALean.NN.Operations.RefinableNetworkLayers

@[expose] public section

/-!
# `neuralNetwork.getRefinableLayers`

CORA's `getRefinableLayers`: the layers whose `is_refinable` is set, in order. The flag is a
constant of a layer's class in CORA (`true` for activation layers, `false` for the others), so it
is the predicate `isRefinable` here, which the caller supplies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layers of `N` that `isRefinable` selects, in order. -/
def RefinableNetwork.refinableLayers (isRefinable : ∀ {a b : ℕ}, RefinableLayer S a b → Bool)
    (N : RefinableNetwork S n m) : List (Σ a b : ℕ, RefinableLayer S a b) :=
  N.layers.filter fun L => isRefinable L.2.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
