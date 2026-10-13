module

public import CORALean.ContSet.Polygon.Real.Theorems.IsCompact

@[expose] public section

/-!
# A polygon is bounded

CORA's `polygon/isBounded` returns `true`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isBounded_construct (P : Polygon) :
    Bornology.IsBounded (ContSet.construct P) :=
  (Polygon.isCompact_construct P).isBounded

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
