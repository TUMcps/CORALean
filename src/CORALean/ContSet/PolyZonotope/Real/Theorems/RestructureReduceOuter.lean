module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RestructureReduce
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureOuter

@[expose] public section

/-!
# `restructureReduce` over-approximates the set

Both steps widen, and neither one's ranking shows: `reduce_outer` holds at every
partition and `restructure_outer` at every set. Which generators the order
argument spends is a question for `restructureReduce_order_le`, not for this
line.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sound at every order, the reduction and the boxing each contributing an
enclosure. -/
theorem PolyZonotope.restructureReduce_outer (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.restructureReduce o).construct :=
  (PolyZonotope.reduce_outer pZ o).trans (PolyZonotope.restructure_outer _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
