module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors

@[expose] public section

/-!
# `ConPolyZono.factorIdx`

The kept factors, indexed by a plain count, as `PolyZonotope`'s is.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept factors, indexed by a plain count, as `PolyZonotope`'s is. -/
def ConPolyZono.factorIdx {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (k : Fin (ConPolyZono.usedFactors E EC).card) : Fin p :=
  PolyZonotope.factorIdx (ConPolyZono.appendE E EC) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
