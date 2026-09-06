import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `ConPolyZono.usedFactors`

The factors either block still reads. `appendE` puts both exponent matrices
over the shared factors, so this is `PolyZonotope.usedFactors` of one matrix
and denotes the union of the two used sets.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors either block still reads. `appendE` puts both exponent matrices
over the shared factors, so this is `PolyZonotope.usedFactors` of one matrix and
denotes the union of the two used sets. -/
def ConPolyZono.usedFactors {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ) :
    Finset (Fin p) :=
  PolyZonotope.usedFactors (ConPolyZono.appendE E EC)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
