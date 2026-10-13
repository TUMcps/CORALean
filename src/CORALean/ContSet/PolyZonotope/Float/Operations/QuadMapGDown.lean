import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown

/-!
# `quadMap`'s generators, rounded down

Split out of `QuadMap.lean` (issue #62): read again by `quadMapGDiff` and
`quadMapDep` in this directory and by `Theorems/QuadMapOuter.lean`, all
outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the image, `Gᵢᵀ Q Gⱼ`, rounded down: `Q *ᵥ Gⱼ` in both
directions first, then the outer product against `Gᵢ` over that interval. -/
def PolyZonotope.quadMapGDown (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ.h + 1) * (pZ.h + 1)) :=
  PolyZonotope.bilinGDown Q pZ pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
