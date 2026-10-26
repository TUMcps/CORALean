module

public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# A formula whose next operators are combined

The shape `combineNext.m` produces: along the `~`, `&`, `|` and `next` nodes of the formula, no
`next` has a `next` or a `~` below it, and none has an `&` or `|` with a temporal operand below
it. The operands of `until`, `release`, `finally` and `globally` are not entered, as in CORA.

## Inputs
* none

## Output
* no next operator is left that could be rewritten
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No `next` is left that `combineNext` would rewrite. -/
def STL.Tree.IsNextCombined : STL.Tree NNReal ℝ n → Prop
  | .next _ (.and φ ψ) | .next _ (.or φ ψ) => (φ.temporal || ψ.temporal) = false
  | .next _ (.not _) | .next _ (.next _ _) => False
  | .not φ => φ.IsNextCombined
  | .and φ ψ | .or φ ψ => φ.IsNextCombined ∧ ψ.IsNextCombined
  | _ => True

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
