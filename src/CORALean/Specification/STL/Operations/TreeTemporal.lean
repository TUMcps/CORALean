module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Whether a formula has a temporal operator

The `temporal` property of CORA's `stl` objects (`@stl/stl.m`): `true` for a formula containing
`until`, `release`, `finally`, `globally` or `next` (the `next` constructor sets it), `false` for
a
comparison, `true`, `false`, and the `~`, `&`, `|` of such.

## Inputs
* none

## Output
* whether the formula has a temporal operator
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

/-- `obj.temporal`. -/
def STL.Tree.temporal : STL.Tree n → Bool
  | .tt | .ff | .cmp _ _ _ => false
  | .not φ => temporal φ
  | .and φ ψ | .or φ ψ => temporal φ || temporal ψ
  | _ => true

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
