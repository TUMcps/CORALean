import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian
import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `PolyZonotope.jacobianMat`

The Jacobian of the point map at a factor vector: column `k` is the point of the derivative
along factor `k` (`jacobian`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.jacobianMat (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) :
    Matrix (Fin n) (Fin pZ.p) ℝ :=
  Matrix.of fun i k => (pZ.jacobian k).point a i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
