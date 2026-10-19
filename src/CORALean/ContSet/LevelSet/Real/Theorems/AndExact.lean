module

public import CORALean.ContSet.LevelSet.Real.Operations.And
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# `LevelSet.and_` is exact

Stacking constraints is intersecting the sets, with equality, whatever the operators.

## Inputs
* `L₁` – first level set
* `L₂` – second level set

## Hypotheses
* none

## Conclusion
* the result denotes the intersection of the two sets
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.and_exact (L₁ L₂ : LevelSet n) :
    (L₁.and_ L₂).construct = L₁.construct ∩ L₂.construct := by
  ext x
  exact LevelSet.forall_append_holds _ _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
