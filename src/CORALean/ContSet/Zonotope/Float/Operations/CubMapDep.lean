import CORALean.ContSet.Zonotope.Float.Operations.CubMapGDiff
import CORALean.ContSet.Zonotope.Float.Operations.CubMapCDown
import CORALean.ContSet.Zonotope.Float.Operations.CubMapCUp
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual

/-!
# `Zonotope.cubMapDep`

CORA's `@zonotope/cubMap` (`aux_cubMapSingle`) at a set whose box is empty, on the stored floats:
the enclosing zonotope of `Real.Zonotope.cubMap`, with centre and generators rounded down and what
that leaves to pay in the box (the centre's gap to its upper rounding, the generators' gaps, which
a coefficient in `[-1, 1]` spreads either way). Sound only where the operand's own box is empty,
so nothing outside `cubMap` calls it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMapDep (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m where
  h := (Z.h + 1) * (Z.h + 1) * (Z.h + 1)
  c := Zonotope.cubMapCDown T Z
  G := fun l i => Zonotope.cubMapGDown T Z i l
  E := (Interval.residual (Zonotope.cubMapCDown T Z) (Zonotope.cubMapCUp T Z)
    (Zonotope.cubMapCDown T Z)).plus (Zonotope.generatorError (Zonotope.cubMapGDiff T Z))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
