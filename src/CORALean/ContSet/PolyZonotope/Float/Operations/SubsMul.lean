import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# `PolyZonotope.subsMul`

CORA's `priv_multiply` on the stored floats: the product of two sums of monomials, one term per
pair. A term is a bracket `(lo, hi)` of its coefficient, which rounding has left unknown, and an
exponent vector; the product's bracket is the pair of directed corner products.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsMul (A B : List ((𝕋 × 𝕋) × (Fin p → ℕ))) :
    List ((𝕋 × 𝕋) × (Fin p → ℕ)) :=
  A.flatMap fun s => B.map fun t =>
    ((Interval.mulLo s.1.1 s.1.2 t.1.1 t.1.2, Interval.mulHi s.1.1 s.1.2 t.1.1 t.1.2), s.2 + t.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
