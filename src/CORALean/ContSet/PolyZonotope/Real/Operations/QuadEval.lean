import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The quadratic map itself

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`Theorems/QuadMapOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic map itself: one matrix per output coordinate. -/
def PolyZonotope.quadEval {n m : ℕ} (Q : Fin m → Mat ℝ n n) (x : Vec ℝ n) : Vec ℝ m :=
  fun k => x ⬝ᵥ (Q k *ᵥ x)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
