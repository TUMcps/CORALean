module

public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtFilter

@[expose] public section

/-!
# The kept-column table is `keepIdx`

Reading `keepTab` of a `repTab` at `j` is `keepIdx`'s answer: the columns a
`repTab` fixes are `repKeep`, listed in order.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
