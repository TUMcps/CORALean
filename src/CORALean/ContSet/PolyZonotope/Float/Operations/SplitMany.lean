import CORALean.ContSet.PolyZonotope.Float.Operations.SplitGen

/-!
# `PolyZonotope.splitMany`, over a floating-point scalar

The pieces `containsPointSet` works with: `k` rounds, every piece replaced by the two halves
`splitGen` gives, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitMany (pZ : PolyZonotope (Vec 𝕋 n)) : ℕ → List (PolyZonotope (Vec 𝕋 n))
  | 0 => [pZ]
  | k + 1 => (pZ.splitMany k).flatMap fun q => [q.splitGen.1, q.splitGen.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
