module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyP

@[expose] public section

/-!
# `PolyZonotope.evalPoly`

Horner's rule, coordinatewise: one coefficient *vector* per degree, lowest degree first, so
every coordinate carries a polynomial of its own. `mul` multiplies coordinatewise and a
coefficient only shifts the center, so the coordinates never mix. `pZ` stays the right factor
at every step, so the shared factor count never moves. The shift goes directly into `c` rather
than through `plus`, which would only reintroduce the identity a direct `c := … + a` already
is. `mul` sets `q := 0`, so `evalPoly` inherits that contract: a caller who needs independent
coefficients to count runs `dependent` once on `pZ` first.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors

## Output
* polynomial zonotope of the polynomial evaluated at the set
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Horner's rule, coordinatewise, coefficients lowest degree first: `[a₀]` is
the constant `a₀`, and `a₀ :: rest` is `a₀ + pZ * evalPoly rest`. -/
def PolyZonotope.evalPoly (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) := (PolyZonotope.evalPolyP pZ coeffs).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
