module

public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Residual
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# What `mtimes` owes beyond its nominal part

Split out of `Mtimes.lean` (issue #62): read again by
`Theorems/MtimesOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the centre, and both generator
blocks. -/
def PolyZonotope.mtimesResidual (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) :=
  ((Interval.residual (mulVecDown M pZ.c) (mulVecUp M pZ.c) (mulVecDown M pZ.c)).plus
      (PolyZonotope.generatorError (matMulDiff M (fun i l => pZ.G l i)))).plus
    (PolyZonotope.generatorError (matMulDiff M (fun i j => pZ.GI j i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
