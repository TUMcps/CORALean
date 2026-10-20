module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `Interval.descProd`, over a floating-point scalar

`descProd` of a sequence of interval matrices, rounded: `A hi * A (hi - 1) * ...`, `d` factors,
recursing on the right as the real `descProd` does, so `Theorems/DescProdOuter` unfolds both the
same way. The empty product is the stored identity block `diagonalBlock fun _ => one`, as in
`Interval.matPow`, and each step is `materialiseMat`d before the next multiplication reads it.

## Inputs
* `A` – family of interval matrices
* `hi` – index of the first factor

## Output
* descending product from index `hi`, as a function of the factor count
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `A hi * A (hi - 1) * ...`, `d` factors, each product rounded outward. -/
def Interval.descProd (A : ℕ → Interval (Mat 𝕋 n n)) (hi : ℕ) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.point (diagonalBlock fun _ => one)
  | d + 1 => (Interval.matMul (A hi) (Interval.descProd A (hi - 1) d)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
