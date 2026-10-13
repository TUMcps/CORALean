import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import Mathlib.Data.Finset.Sort

/-!
# `PolyZonotope.boxOutRadius`, over a floating-point scalar

The radius of the box `PolyZonotope.boxOut` appends in each coordinate: the directed-up sum of the
absolute values of the removed dependent and the taken independent generators.
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

/-- The radius of the box in coordinate `i`, rounded up. -/
def PolyZonotope.boxOutRadius (pZ : PolyZonotope (Vec 𝕋 n)) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : Vec 𝕋 n := fun i =>
  addUp (sumUp fun l => if removed l then absolute (pZ.G l i) else zero)
    (sumUp fun j => if taken j then absolute (pZ.GI j i) else zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
