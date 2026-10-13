module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The quadratic map itself

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`Theorems/QuadMapOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic map itself: one matrix per output coordinate. -/
def PolyZonotope.quadEval {n m : ℕ} (Q : Fin m → Mat ℝ n n) (x : Vec ℝ n) : Vec ℝ m :=
  fun k => x ⬝ᵥ (Q k *ᵥ x)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
