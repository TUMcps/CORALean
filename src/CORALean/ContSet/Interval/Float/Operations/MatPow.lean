import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `Interval.matPow`, over a floating-point scalar

`Real.Interval.matPow` rounded: recurses on the right, `A * (A ^ k)`, matching
the exact layer so `Theorems/MatPowOuter` can unfold the left factor the same
way. No `Monoid`/`Pow` instance behind it, `matMul` not being associative up to
equality.

The base case is `diagonalBlock fun _ => one`, not `(1 : Mat 𝕋 n n)`: `𝕋` has no
generic `One`/`Zero` instance (`FloatOps`'s own docstring — one would collide
with ℝ's), so a float identity matrix has to be built from `diagonalBlock`, as
`identityMat` already does elsewhere.

Each step's bounds are `materialiseMat`d before the next multiplication reads
them: `matMul` builds a closure over its two operands, so left unmaterialised
the recursion would nest `k` closures deep by the time `matPow A k` is read.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matPow (A : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.point (diagonalBlock fun _ => one)
  | k + 1 => (Interval.matMul A (Interval.matPow A k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
