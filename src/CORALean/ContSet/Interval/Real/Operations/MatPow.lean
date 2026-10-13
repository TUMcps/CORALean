import CORALean.ContSet.Interval.Real.Operations.MatMul
import CORALean.ContSet.Interval.Real.Operations.Point
import Mathlib.Data.Matrix.Diagonal

/-!
# `Interval.matPow`

The recursive power of an interval matrix, with no `Monoid`/`Pow` instance
behind it: `matMul` is not associative up to equality, only up to mutual
enclosure, so nothing here could be a lawful `Pow`.

**Recurses on the right, `A * (A ^ k)`, not `(A ^ k) * A`.** This is not
cosmetic: the two associations enclose different sets, since each product
bounds its summands independently and so loses precision at a different place,
and `Theorems/MatPowOuter` unfolds the left factor to match.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matPow (A : Interval (Mat ℝ n n)) : ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.point 1
  | k + 1 => Interval.matMul A (Interval.matPow A k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
