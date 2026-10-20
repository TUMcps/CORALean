module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.reduce` over-approximates

Above the order it is the zonotope's `reduce` composed with forgetting the
constraints, both enclosures; at or below it, the identity.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.reduce o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduce
  split_ifs with hlt
  · rw [← Zonotope.conZonotope_exact]
    exact subset_trans (ConZonotope.zonotope_contains cZ) (Zonotope.reduce_outer cZ.zonotope o)
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
