module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
public import CORALean.ContSet.ConZonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.quadMapCUp`

The center of `quadMapCDown` rounded up; the box the stored center needs is the gap
between the two.

## Inputs
* `Q` – quadratic form matrices
* `cZ` – float constrained zonotope

## Output
* center of the quadratic image rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center of the enclosing zonotope, from above. -/
def ConZonotope.quadMapCUp (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Vec 𝕋 m :=
  fun i => addUp (ConZonotope.quadBilUp (Q i) cZ.c cZ.c)
    (half (sumUp fun s => ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
