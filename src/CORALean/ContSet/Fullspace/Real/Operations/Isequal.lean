module

public import CORALean.ContSet.Fullspace.Real.Fullspace

@[expose] public section

/-!
# `Fullspace.isequal`

CORA's `@fullspace/isequal` at two full spaces: `true`, their dimensions agreeing. The dimension is
the index, so two operands of one type agree on it; the other operand types of CORA's method
(an `interval` with all endpoints infinite, other sets and numerics, which answer `false`) are
not covered.

## Inputs
* `_` – first full space
* `_` – second full space

## Output
* `true`, as two full spaces are equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/isequal` at another full space of the same dimension. -/
def Fullspace.isequal (_ _ : Fullspace n) : Bool := true

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
