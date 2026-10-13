module

public import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

@[expose] public section

/-!
# The generators of `quadMap`

`bilinG` at the quadratic form family, one set paired with itself. Which
bilinear map is paired is the only thing separating a quadratic map from a
coordinatewise or a matrix product, so `quadMap` is `bilin` at `quadBilin` and
this is where that choice is made.

Its own file (issue #62): read again by the float layer's own
`Theorems/QuadMapOuter.lean` and by `ConPolyZono.quadMapDep`, both outside this
file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the image: `Gᵢᵀ Q Gⱼ`, one coordinate per matrix. -/
def PolyZonotope.quadMapG (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    Fin ((pZ.h + 1) * (pZ.h + 1)) → Vec ℝ m :=
  PolyZonotope.bilinG (PolyZonotope.quadBilin Q) pZ pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
