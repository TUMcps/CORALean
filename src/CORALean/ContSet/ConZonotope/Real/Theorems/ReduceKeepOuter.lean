module

public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeep
public import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepByOuter

@[expose] public section

/-!
# `ConZonotope.reduceKeep` over-approximates

Above the order it is `reduceKeepBy` at `step_keepSplit`, an over-approximation at every
partition; at or below it, the identity.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceKeep_outer (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    cZ.construct ⊆ (cZ.reduceKeep o).construct := by
  unfold ConZonotope.reduceKeep
  split_ifs with hlt
  · exact ConZonotope.reduceKeepBy_outer cZ _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
