module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.PolyZonotope.Float.Theorems.RepTabGetD
public import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtKeepTab

@[expose] public section

/-!
# `compactCons` is its specification

The tabulated merge and the one that rescans return the same set: the tables hold
the very values the specification recomputes, so the two differ in cost alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactCons_eq_spec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.compactCons = cPZ.compactConsSpec := by
  simp only [ConPolyZono.compactCons, ConPolyZono.compactConsSpec,
    ConPolyZono.compactConsB, PolyZonotope.repTab_getD, PolyZonotope.tabAt_keepTab]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
