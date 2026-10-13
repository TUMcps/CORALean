module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo

@[expose] public section

/-!
# `Interval.matMul`, over a floating-point scalar

`Real.Interval.matMul` rounded: entry `(i, j)` is the sum over `k` of the corner
hull of `A`'s `(i, k)` interval against `B`'s `(k, j)` one, each hull `mulLo`/
`mulHi` and the row itself summed with `sumDown`/`sumUp` — two roundings per
entry, the corner and the row.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matMul (A : Interval (Mat 𝕋 m n)) (B : Interval (Mat 𝕋 n p)) :
    Interval (Mat 𝕋 m p) where
  inf := fun i j => sumDown fun k => Interval.mulLo (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)
  sup := fun i j => sumUp fun k => Interval.mulHi (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
