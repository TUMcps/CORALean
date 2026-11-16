module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# One neuron's row of a polynomial zonotope, as lists

CORA evaluates the polynomial of a neuron on its row of the set: the center `c`, the dependent
generators `G` and the independent ones `GI` of that coordinate, without the exponents, which do
not depend on the row (`PolyZonotope.powerOut`). The entries are of any type, so a row of column
vectors holds all neurons at once.
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The center, the dependent and the independent generators of a row. -/
structure PowerRow (α : Type) where
  c : α
  G : List α
  GI : List α

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
