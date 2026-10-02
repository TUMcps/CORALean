import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius

/-!
# `Interval.intervalMatrix`

CORA's `@interval/intervalMatrix`: the interval matrix with the interval's centre and half-width,
`intervalMatrix(center(I), rad(I))`. It denotes the same set, since the centre and half-width of a
box give its bounds back (`Theorems/IntervalMatrixEq`).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.intervalMatrix (I : Interval α) : Interval α :=
  Interval.ofCenterRadius I.center I.radius

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
