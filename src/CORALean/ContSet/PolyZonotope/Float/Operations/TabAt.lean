import Mathlib.Data.Finset.Sort

/-!
# A sorted finset's `j`-th element, read off a table

`Finset.orderIsoOfFin` re-sorts its finset at every call; a caller that wants
the `j`-th element of the same finset many times builds its elements into an
`Array` once and reads them back here (issue #61). The default stands for an
index past the table's end, which a table of the right length never reaches.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `j`-th element of `s`, as `t` lists them. -/
def PolyZonotope.tabAt (s : Finset (Fin h)) (t : Array (Fin h)) (j : Fin s.card) : Fin h :=
  t.getD j.val (Fin.castLE (by simpa using Finset.card_le_univ s) j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
