import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

/-!
# `PolyZonotope.evalPoly`

The exact layer's Horner step, `mul` then a centre shift, rounded exactly as
`mul`/`plus` round it — except one thing neither of those owes on its own:
`R`, here, is itself only known to within its own error box, not exact, so
multiplying it by `pZ` also multiplies that uncertainty by however large `pZ` can
be. `evalPolyBoundS` bounds `|nominal pZ|` entrywise, and the extra box
`errorBound R.err * evalPolyBoundS pZ` is what a plain `mul` call would drop.

`c` rounds down, matching `plus`'s own centre; `mul`'s box and this one and the
centre's residual all add through `Interval.plus`, never combined into fewer
generators.

A coefficient is a vector, one entry per coordinate, as over ℝ: the shift is
entrywise, so the coordinates round independently and each carries its own
polynomial.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Horner's rule, coordinatewise, coefficients lowest degree first, rounded. -/
def PolyZonotope.evalPoly (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) := (PolyZonotope.evalPolyP pZ coeffs).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
