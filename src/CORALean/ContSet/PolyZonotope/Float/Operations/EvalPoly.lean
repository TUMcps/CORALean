module

public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

@[expose] public section

/-!
# `PolyZonotope.evalPoly`

The exact layer's Horner step, `mul` then a center shift, rounded as `mul`/`plus` round it,
except that `R` is itself only known to within its own error box, so multiplying it by `pZ`
also multiplies that uncertainty. `evalPolyBoundS` bounds `|nominal pZ|` entrywise, and the
extra box `errorBound R.err * evalPolyBoundS pZ` is what a plain `mul` would drop. `c` rounds
down, matching `plus`. A coefficient is a vector, as over ℝ: the shift is entrywise, so the
coordinates round independently.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors

## Output
* polynomial zonotope of the polynomial evaluated at the set
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Horner's rule, coordinatewise, coefficients lowest degree first, rounded. -/
def PolyZonotope.evalPoly (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) := (PolyZonotope.evalPolyP pZ coeffs).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
