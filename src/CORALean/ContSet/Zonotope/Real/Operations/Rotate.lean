import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.RotMat

/-!
# `Zonotope.rotate`

CORA's `@zonotope/rotate(Z, dims, angle)`: the rotation is applied to the centre and the generators
on the two coordinates `dims`, the others being left alone. That is `mtimes` at `rotMat`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/rotate`. -/
noncomputable def Zonotope.rotate {n : ℕ} (Z : Zonotope (Vec ℝ n)) (i j : Fin n) (angle : ℝ) :
    Zonotope (Vec ℝ n) :=
  Zonotope.mtimes (rotMat n i j angle) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
