import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset

/-!
# `PolyZonotope.resolve`, over a floating-point scalar

Factor `k` fixed at the value `x`: `getSubset` at `[x, x]`, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.resolve (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) (x : 𝕋) : PolyZonotope 𝕋 n :=
  pZ.getSubset k x zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
