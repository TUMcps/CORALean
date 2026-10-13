import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap

/-!
# `VPolytope.mtimes`

The matrix applied to every vertex, rounded down, with the gap charged to the
box — the box itself going through the interval `mtimes`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.mtimes (M : Mat 𝕋 m n) (P : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 m) where
  k := P.k
  V := fun l => mulVecDown M (P.V l)
  E := (Interval.mtimes M P.E).plus
        (VPolytope.columnGap (fun l => mulVecDown M (P.V l)) fun l => mulVecUp M (P.V l))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
