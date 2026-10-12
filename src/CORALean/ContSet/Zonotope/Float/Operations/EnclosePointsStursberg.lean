import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# `Zonotope.enclosePointsStursberg`, over a floating-point scalar

CORA's `@zonotope/enclosePoints.m` at `method = 'stursberg'`, on the stored floats: the points are
centred on their mean, rotated by `Uᵀ`, boxed per rotated coordinate by the minimum and maximum
over the points, and the box is rotated back by `U` and moved to the mean.

The mean is rounded up from the sum (the count is the float sum of ones), and each centred point
is held in the interval between its two directed differences, so the rotation `Uᵀ` is the interval
`mtimes`. Nothing in the enclosure depends on the mean or on the basis being the SVD's: the
points lie in the result whenever `U Uᵀ = 1` over the reals. As at the real layer `U` is an
argument, and at least one point is required.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclosePoints(points, 'stursberg')` for a given basis `U`. -/
def Zonotope.enclosePointsStursberg [NeZero N] (pts : Fin N → Vec 𝕋 n) (U : Mat 𝕋 n n) :
    Zonotope 𝕋 n :=
  let count : 𝕋 := sumUp fun _ : Fin N => one
  let mean : Vec 𝕋 n := fun i => divUp (sumUp fun j => pts j i) count
  -- the centred points, each between its two directed differences
  let sampleMatrix : Fin N → Interval (Vec 𝕋 n) := fun j =>
    ⟨fun i => subDown (pts j i) (mean i), fun i => subUp (pts j i) (mean i)⟩
  let orientedMatrix : Fin N → Interval (Vec 𝕋 n) := fun j =>
    Interval.mtimes U.transpose (sampleMatrix j)
  let box : Interval (Vec 𝕋 n) :=                                -- [m2, m1]
    ⟨fun i => minimumOver fun j => (orientedMatrix j).inf i,
     fun i => maximumOver fun j => (orientedMatrix j).sup i⟩
  (Zonotope.mtimes U box.zonotope).plus (Zonotope.point mean)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
