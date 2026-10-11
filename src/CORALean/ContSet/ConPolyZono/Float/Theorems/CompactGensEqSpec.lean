import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepTabGetD
import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtKeepTab

/-!
# `compactGens` is its specification

The tabulated merge and the one that rescans return the same set: the tables hold
the very values the specification recomputes, so the two differ in cost alone.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactGens_eq_spec (cPZ : ConPolyZono 𝕋 n) :
    cPZ.compactGens = cPZ.compactGensSpec := by
  simp only [ConPolyZono.compactGens, ConPolyZono.compactGensSpec, ConPolyZono.mergedCol,
    PolyZonotope.repTab_getD, PolyZonotope.tabAt_keepTab]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
