module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Conjoining a list of formulas

The idiom `res = []; for ..., res = res & c; end` of `polytope2stl.m`: `[] & c` is `c`, and
`res & c` the conjunction. The empty list leaves `res = []`, which stands for no constraint, and
is
`true` here.

## Inputs
* `L` – list of formulas

## Output
* the left-nested conjunction, true for an empty list
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The left-nested conjunction of the list, `true` for the empty list. -/
def STL.Tree.conjoin (L : List (STL.Tree τ κ n)) : STL.Tree τ κ n :=
  (L.foldl (fun res c => some (res.elim c fun r => .and r c)) none).getD .tt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
