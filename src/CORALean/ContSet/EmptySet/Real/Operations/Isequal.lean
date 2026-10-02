import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.isequal`

CORA's `@emptySet/isequal` at two empty sets: `true`, their dimensions agreeing. The dimension is
the index, so two operands of one type agree on it; the other operand types of CORA's method
(a set that represents `∅`, a numeric empty matrix) are not covered.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/isequal` at another empty set of the same dimension. -/
def EmptySet.isequal (_ _ : EmptySet n) : Bool := true

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
