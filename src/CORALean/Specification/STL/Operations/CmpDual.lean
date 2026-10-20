module

public import CORALean.Specification.STL.Definitions.Cmp

@[expose] public section

/-!
# The comparison with the sides swapped

`a < b` is `b > a` and `a ≤ b` is `b ≥ a`: the swap CORA's `lt`, `le`, `gt` and `ge` make when the
number stands on the left of an `stl` operand.

## Inputs
* none

## Output
* the comparison with the sides swapped
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The comparison read from the other side. -/
def STL.Cmp.dual : STL.Cmp → STL.Cmp
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
