import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.ofIntervalMat`

CORA's `matZonotope(intervalMatrix)`: the centre matrix, and one generator per entry
carrying that entry's radius there and zero elsewhere, so that a product of matrix
zonotopes keeps each entry's dependence on itself. The centre is `centreMat`, whose
rounding the radius absorbs: the radius is the larger magnitude of `I - centre`'s
bounds (`matResidual`), and `maximum`/`absolute` are exact, so the box stays zero.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre matrix, and one generator per entry holding that entry's radius. -/
def Zonotope.ofIntervalMat (I : Interval (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 m n) :=
  let C := Interval.centreMat I                                   -- the centre, stored
  let Rs := Interval.matResidual I.inf I.sup C                    -- I - C, a box
  let r : Mat 𝕋 m n := fun i j => maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))
  { h := m * n
    c := C
    G := fun k i j => if finProdFinEquiv (i, j) = k then r i j else zero
    E := Interval.point fun _ _ => zero }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
