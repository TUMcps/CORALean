import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx

/-!
# The kept columns as a table, over a floating-point scalar

The columns whose table entry is themselves, in column order: `repKeep` listed
instead of re-derived, which is what `keepIdx` does at every call (issue #61).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The columns a `repTab` fixes, in increasing order: the table `keepIdx` is
read from. -/
def PolyZonotope.keepTab (t : Array (Fin h)) : Array (Fin h) :=
  ((List.finRange h).filter fun j => decide (t.getD j.val j = j)).toArray

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
