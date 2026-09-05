import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors

/-!
# `ConPolyZono.factorExtend`

A factor vector over the kept factors, read back over all of them by giving a
dropped factor the value zero — admissible, and read by no monomial of either
block.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

/-- A factor vector over the kept factors, read back over all of them by giving a
dropped factor the value zero — admissible, and read by no monomial of either
block. -/
def ConPolyZono.factorExtend {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (k : Fin p) : ℝ :=
  PolyZonotope.factorExtend (ConPolyZono.appendE E EC) a k

end CORALean.Real
