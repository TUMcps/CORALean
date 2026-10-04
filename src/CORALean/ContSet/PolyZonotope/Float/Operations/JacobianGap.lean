import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# What `PolyZonotope.jacobian` can be off by

The generator column `i` of the derivative along factor `k` is the exponent `E k i` times the
stored column. A float has no natural-number cast, so the product is the `E k i`-fold sum of the
column: stored with the lower rounding, bounded above by the upper one, and the gap between them is
what the box pays.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The gap between the two directed multiples of a column. -/
def PolyZonotope.jacobianGap (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) : Mat 𝕋 n pZ.h :=
  fun r i => subUp (sumUp fun _ : Fin (pZ.E k i) => pZ.G r i)
    (sumDown fun _ : Fin (pZ.E k i) => pZ.G r i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
