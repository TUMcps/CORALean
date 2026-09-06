import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

/-!
# `PolyZonotope.evalPoly`

The exact layer's Horner step, `mul` then a centre shift, rounded exactly as
`mul`/`plus` round it — except one thing neither of those owes on its own:
`R`, here, is itself only known to within its own error box, not exact, so
multiplying it by `S` also multiplies that uncertainty by however large `S` can
be. `evalPolyBoundS` bounds `|nominal S|` entrywise, and the extra box
`errorBound R.err * evalPolyBoundS S` is what a plain `mul` call would drop.

`c` rounds down, matching `plus`'s own centre; `mul`'s box and this one and the
centre's residual all add through `Interval.plus`, never combined into fewer
generators.

A coefficient is a vector, one entry per coordinate, as over ℝ: the shift is
entrywise, so the coordinates round independently and each carries its own
polynomial.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Horner's rule, coordinatewise, coefficients lowest degree first, rounded. -/
def PolyZonotope.evalPoly (S : PolyZonotope 𝕋 n) (coeffs : List (Vec 𝕋 n)) :
    PolyZonotope 𝕋 n := (PolyZonotope.evalPolyP S coeffs).1

end CORALean.Float
