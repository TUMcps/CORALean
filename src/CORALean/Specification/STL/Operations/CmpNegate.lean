module

public import CORALean.Specification.STL.Definitions.Cmp

@[expose] public section

/-!
# The negated comparison

`¬(a < b)` is `a ≥ b`, `¬(a ≤ b)` is `a > b`: the comparison that holds exactly where this one
fails.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The comparison that holds exactly where this one does not. -/
def STL.Cmp.negate : STL.Cmp → STL.Cmp
  | .lt => .ge
  | .le => .gt
  | .gt => .le
  | .ge => .lt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
