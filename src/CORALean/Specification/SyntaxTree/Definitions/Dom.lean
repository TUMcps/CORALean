module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The interval a node stores

The `interval` (CORA's class) a node of a `syntaxTree` stores: one-dimensional, over the real-layer
`Interval`. It has no infinite bound, which `syntaxTree.m` allows for an unbounded domain.

## Inputs
* none

## Output
* the one-dimensional interval a node stores
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `interval` a node stores. -/
abbrev SyntaxTree.Dom := Real.Interval (Vec ℝ 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
