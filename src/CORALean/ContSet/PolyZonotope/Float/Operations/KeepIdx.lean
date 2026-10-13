module

public import CORALean.ContSet.PolyZonotope.Float.Operations.RepKeep
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# The kept columns, indexed by a plain count, over a floating-point scalar

Split out of `Compact.lean` (issue #62): read again by `mergedCol` and
`mergedColUp` in this directory, and by `Theorems/CompactGensOuter.lean` and
`ConPolyZono`'s own compaction, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept columns indexed by a plain count, which is what the field `h` needs
and a `Finset` is not. -/
def PolyZonotope.keepIdx (E : Fin p → Fin h → ℕ)
    (j : Fin (PolyZonotope.repKeep E).card) : Fin h :=
  (PolyZonotope.repKeep E).orderIsoOfFin rfl j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
