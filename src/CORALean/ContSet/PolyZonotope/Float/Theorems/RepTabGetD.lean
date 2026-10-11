import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab

/-!
# A `repTab` entry is `rep`

The table agrees with the function it tabulates, which is all a reader of it needs.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.repTab_getD (E : Fin p → Fin h → ℕ) (l : Fin h) :
    (PolyZonotope.repTab E).getD l.val l = Real.PolyZonotope.rep E l := by
  simp [PolyZonotope.repTab, Array.getD_eq_getD_getElem?]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
