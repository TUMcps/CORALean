module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# `Zonotope.reduceAdaptive` keeps the set it had

CORA's adaptive rule only chooses which generators to box; `reduceBy` is sound at every partition,
so the result holds the set whatever the rule chose, at every `diagpercent` and precision.

## Inputs
* `Z` – zonotope
* `diagpercent` – admissible distance, relative to the box diagonal
* `p` – square root precision

## Hypotheses
* none

## Conclusion
* zonotope is contained in its adaptive reduction
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The adaptive reduction of `Z` holds `Z`. -/
theorem Zonotope.reduceAdaptive_outer (Z : Zonotope (Vec 𝕋 n)) (diagpercent : 𝕋) (p : ℕ) :
    Z.toSet ⊆ (Z.reduceAdaptive diagpercent p).toSet :=
  Z.reduceBy_outer _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
