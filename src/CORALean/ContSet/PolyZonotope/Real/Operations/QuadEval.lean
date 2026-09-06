import CORALean.Global.Tensor

/-!
# The quadratic map itself

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`Theorems/QuadMapOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

/-- The quadratic map itself: one matrix per output coordinate. -/
def PolyZonotope.quadEval {n m : ℕ} (Q : Fin m → Mat ℝ n n) (x : Vec ℝ n) : Vec ℝ m :=
  fun k => x ⬝ᵥ (Q k *ᵥ x)

end CORALean.Real
