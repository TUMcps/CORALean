module

@[expose] public section

/-!
# `NonlinearReset.Arg`: a state or input argument of `evaluate`

The arguments `x`, `u` of `nonlinearReset/evaluate` are a `contSet` (here its center, the
expansion point `center(x)`) or numeric (`isnumeric`, here the vector itself).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A set given by its center, or a numeric vector. -/
inductive NonlinearReset.Arg (E : Type) where
  | set (center : E)
  | num (v : E)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
