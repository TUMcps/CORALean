module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtKeepTab

@[expose] public section

/-!
# `PolyLevelSet.compact` is its specification

The tabulated merge and the one that rescans return the same set: the tables hold the very values
the specification recomputes (`repTab_getD`, `tabAt_keepTab`), so the two differ in cost alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The tabulated merge is its specification. -/
theorem PolyLevelSet.compact_eq_spec (P : PolyLevelSet 𝕋 n) : P.compact = P.compactSpec := by
  simp only [PolyLevelSet.compact, PolyLevelSet.compactSpec, PolyZonotope.repTab_getD,
    PolyZonotope.tabAt_keepTab]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
