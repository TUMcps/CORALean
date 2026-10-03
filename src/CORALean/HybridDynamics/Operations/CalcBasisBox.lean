import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# `Location.calcBasisBox`

CORA's `@location/calcBasis.m` at `options.enclose{i} = 'box'`: `B{i} = eye(sys.nrOfDims)`, the
identity, so the guard intersection is enclosed in the coordinate directions. The `'pca'` case
(the left singular vectors of the reachable set's generators, `svd([-G, G])`) and the `'flow'`
case (a Gram-Schmidt basis of the flow direction) are not modelled, and `calcBasis` returns one
basis per entry of `options.enclose`, of which this is the `'box'` entry.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eye(n)`, the `'box'` basis of `n` dimensions. -/
def Location.calcBasisBox (n : ℕ) : Mat ℝ n n := fun i j => if i = j then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
