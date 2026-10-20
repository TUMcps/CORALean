module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `Interval.matPow`, over a floating-point scalar

`Real.Interval.matPow` rounded: recurses on the right, `A * (A ^ k)`, matching the exact layer so
`Theorems/MatPowOuter` can unfold the left factor the same way. The base case is
`diagonalBlock fun _ => one`, not `(1 : Mat 𝕋 n n)`, as `𝕋` has no generic `One`/`Zero` instance.
Each step is `materialiseMat`d before the next multiplication reads it, so that `matPow A k` does
not nest `k` closures.

## Inputs
* `A` – interval matrix

## Output
* interval matrix power of `A`, as a function of the exponent
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
