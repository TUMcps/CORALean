module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceByOuter
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# Girard's reduction over-approximates

Two cases: below the order there is nothing to do, and above it the rule is a
pair of partitions like any other, so `reduceBy_outer` closes it. The metric
never appears, which is what leaves the ranking free to be a heuristic.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_outer (cPZ : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    cPZ.construct ⊆ (cPZ.reduceGirard o).construct := by
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact ConPolyZono.reduceBy_outer cPZ _ _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
