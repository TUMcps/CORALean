module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `PolyZonotope.subsMul`

CORA's `priv_multiply` on the stored floats: the product of two sums of monomials, one term per
pair. A term is a bracket `(lo, hi)` of its coefficient, which rounding has left unknown, and an
exponent vector; the product's bracket is the pair of directed corner products.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The product of two float term lists: every term of `A` times every term of `B`, with the
exponent vectors added and the coefficient interval the directed-rounding product
(`Interval.mulLo`, `Interval.mulHi`) of the two coefficient intervals. -/
def PolyZonotope.subsMul (A B : List ((Interval 𝕋) × (Fin p → ℕ))) :
    List ((Interval 𝕋) × (Fin p → ℕ)) :=
  A.flatMap fun s => B.map fun t =>
    (⟨Interval.mulLo s.1.inf s.1.sup t.1.inf t.1.sup, Interval.mulHi s.1.inf s.1.sup t.1.inf
        t.1.sup⟩, s.2 + t.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
