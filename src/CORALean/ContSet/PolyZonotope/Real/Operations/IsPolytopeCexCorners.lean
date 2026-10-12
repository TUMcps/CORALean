import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic

/-!
# The hull vertices of `isPolytopeCex`

The four factor assignments whose corner images `(±3, ±1)` `convhulln` keeps (see
`PolyZonotope.isPolytopeCex`); recomputing the hull is not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The hull vertices `(3, 1)`, `(3, -1)`, `(-3, 1)`, `(-3, -1)` as factors `(a, b, c)`. -/
def PolyZonotope.isPolytopeCexCorners : Fin 4 → Fin 3 → ℝ :=
  ![(![1, 1, 1] : Fin 3 → ℝ), (![1, 1, -1] : Fin 3 → ℝ), (![-1, -1, -1] : Fin 3 → ℝ),
    (![-1, -1, 1] : Fin 3 → ℝ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
