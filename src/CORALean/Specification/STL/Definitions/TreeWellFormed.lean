module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Formulas whose time intervals are non-empty

Every `[a,b]` of the formula has `a ≤ b`. CORA's `stlInterval` does not demand it (an interval
with `a > b` is empty); with an empty interval `finally(true)` is false and `globally(false)`
true, which `eliminateTrueFalse` does not account for.

## Inputs
* none

## Output
* every time interval of the formula is nonempty
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

/-- Every time interval of the formula is non-empty. -/
def STL.Tree.IsWellFormed : STL.Tree NNReal ℝ n → Prop
  | .tt => True
  | .ff => True
  | .cmp _ _ _ => True
  | .not φ => φ.IsWellFormed
  | .and φ ψ => φ.IsWellFormed ∧ ψ.IsWellFormed
  | .or φ ψ => φ.IsWellFormed ∧ ψ.IsWellFormed
  | .until a b φ ψ => a ≤ b ∧ φ.IsWellFormed ∧ ψ.IsWellFormed
  | .release a b φ ψ => a ≤ b ∧ φ.IsWellFormed ∧ ψ.IsWellFormed
  | .finally a b φ => a ≤ b ∧ φ.IsWellFormed
  | .globally a b φ => a ≤ b ∧ φ.IsWellFormed
  | .next _ φ => φ.IsWellFormed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
