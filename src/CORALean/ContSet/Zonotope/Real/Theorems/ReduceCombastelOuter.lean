module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# Combastel's reduction over-approximates

The same two cases as Girard's, at a different ranking. That the two proofs are
word for word the same is the evidence for `reduceBy_outer` being stated at an
arbitrary partition rather than at either metric.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* `Z` lies in the reduced zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Same two cases, at Combastel's partition instead of Girard's — the metric
never appears, which is `reduceBy_outer`'s whole point. -/
theorem Zonotope.reduceCombastel_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceCombastel o).construct := by
  unfold Zonotope.reduceCombastel
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
