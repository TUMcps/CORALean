import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap

/-!
# `VPolytope.mtimes`

The matrix applied to every vertex, rounded down, with the gap charged to the
box — the box itself going through the interval `mtimes`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.mtimes (M : Mat 𝕋 m n) (P : VPolytope 𝕋 n) : VPolytope 𝕋 m where
  k := P.k
  V := matMulDown M P.V
  E := (Interval.mtimes M P.E).plus
        (VPolytope.columnGap (matMulDown M P.V) (matMulUp M P.V))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
