import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapDep
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent

/-!
# `PolyZonotope.cubMap`, over a floating-point scalar

CORA's `@polyZonotope/cubMap`, `{ z = (xᵀ T x) * x | x ∈ pZ }` with `zᵢ = Σₖ xₖ (xᵀ T{i,k} x)`, as
`quadMap` is: independent generators and the error box are made dependent first (`dependent`),
then `cubMapDep`. CORA keeps independent generators independent and encloses their cubic terms by
a zonotope; here the result is an enclosure of the image of the whole set, box included.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cubMap (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) := PolyZonotope.cubMapDep T pZ.dependent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
