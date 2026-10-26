module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The interval a node stores, over a float scalar

The one-dimensional `Interval` of floats a node of a `Float.SyntaxTree` stores: a vector of length
one over `𝕋`, with no infinite bound.

## Inputs
* `𝕋` – scalar of the stored bounds

## Output
* the one-dimensional interval of floats a node stores
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval of floats a node stores. -/
abbrev SyntaxTree.Dom (𝕋 : Type) := Interval (Vec 𝕋 1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
