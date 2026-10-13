module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# What `PolyZonotope.jacobian` can be off by

The generator column `i` of the derivative along factor `k` is the exponent `E k i` times the
stored column. A float has no natural-number cast, so the product is the `E k i`-fold sum of the
column: stored with the lower rounding, bounded above by the upper one, and the gap between them is
what the box pays.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The gap between the two directed multiples of a column. -/
def PolyZonotope.jacobianGap (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) : Mat 𝕋 n pZ.h :=
  fun r i => subUp (sumUp fun _ : Fin (pZ.E k i) => pZ.G i r)
    (sumDown fun _ : Fin (pZ.E k i) => pZ.G i r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
