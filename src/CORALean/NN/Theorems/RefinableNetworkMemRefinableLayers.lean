import CORALean.NN.Operations.RefinableNetworkRefinableLayers

/-!
# The refinable layers are exactly the flagged ones

A layer is listed iff it is a layer of the network and `isRefinable` holds of it: nothing flagged
is missing and nothing unflagged is listed. The list is a filter, so the order of the layers is
kept.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Membership in `refinableLayers`: a layer of `N` that is flagged. -/
theorem RefinableNetwork.mem_refinableLayers_iff
    (isRefinable : ∀ {a b : ℕ}, RefinableLayer S a b → Bool) (N : RefinableNetwork S n m)
    (L : Σ a b : ℕ, RefinableLayer S a b) :
    L ∈ N.refinableLayers isRefinable ↔ L ∈ N.layers ∧ isRefinable L.2.2 = true := by
  simp [RefinableNetwork.refinableLayers, List.mem_filter]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
