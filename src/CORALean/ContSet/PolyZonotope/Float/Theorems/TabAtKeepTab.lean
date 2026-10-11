import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepTabGetD
import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtFilter

/-!
# The kept-column table is `keepIdx`

Reading `keepTab` of a `repTab` at `j` is `keepIdx`'s answer: the columns a
`repTab` fixes are `repKeep`, listed in order.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.tabAt_keepTab (E : Fin p → Fin h → ℕ)
    (j : Fin (PolyZonotope.repKeep E).card) :
    PolyZonotope.tabAt (PolyZonotope.repKeep E) (PolyZonotope.keepTab (PolyZonotope.repTab E)) j
      = PolyZonotope.keepIdx E j :=
  PolyZonotope.tabAt_filter _ _
    (fun x => by
      rw [PolyZonotope.repKeep, Finset.mem_filter]
      simp only [decide_eq_true_eq, PolyZonotope.repTab_getD, Finset.mem_univ, true_and]) j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
