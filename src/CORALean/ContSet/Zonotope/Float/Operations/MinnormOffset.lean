import CORALean.ContSet.Zonotope.Float.Operations.FacetNormal
import CORALean.Global.Float.Sqrt

/-!
# `Zonotope.minnormOffset`, over a floating-point scalar

One entry of the vector `b` that `minnorm` takes its minimum over: the offset `Δd = Σᵤ |C G⁽ᵘ⁾|` of
`polytope(Z - c)` at a facet normal `C`, divided by `‖C‖₂` so the row is a unit row. Here it is
rounded up: the numerator by `dotUp` and `dotDown` (the magnitude of a dot product is at most the
larger of the upper end and the negated lower end), the length from below by `sqrtDown` of the
rounded-down square sum. `none` where `ltStrict` cannot prove the length positive, which is where
CORA's row is `NaN` (a zero normal). For any vector `C` the quotient bounds the radius of every
ball around the centre inside the zonotope (`minnormOffset_ge`), so `C` need not be the normal.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m` and `contSet/@zonotope/polytope.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset of the unit-length facet row at generator selection `S`, rounded up; `p` is the
number of Newton steps of the root. -/
def Zonotope.minnormOffset (p : ℕ) (Z : Zonotope (Vec 𝕋 (n + 1)))
    (S : Fin n → Fin Z.h) : Option 𝕋 :=
  let C := Z.facetNormal S                                                  -- facet normal
  let Δd := sumUp fun υ =>                                                  -- Σᵤ |C G⁽ᵘ⁾|
    maximum (dotUp C (Z.G υ)) (neg (dotDown C (Z.G υ)))
  let len := sqrtDown p (dotDown C C)                                       -- ‖C‖₂, from below
  if ltStrict zero len = true then some (divUp Δd len) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
