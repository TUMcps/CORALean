import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyP

/-!
# `PolyZonotope.evalPoly`

Horner's rule, coordinatewise: one coefficient *vector* per degree, lowest
degree first, so every coordinate carries a polynomial of its own. `mul`
multiplies coordinatewise and a coefficient only shifts the centre, so the
coordinates never mix and an activation layer can give each neuron the fit its
own input range earned. `S` stays the right factor at every step, so the shared
factor count `S.p` never moves and every step's `hp` is the previous one's,
carried along rather than reproved.

That shift goes directly into `c` rather than through `plus`: a constant carries
no generators and no factors of its own, so `plus`'s block-diagonal bookkeeping
would only reintroduce, via `Fin.append`, the identity a direct `c := … + a`
already is. `map` is unneeded too — Horner never scales a whole accumulated set.

`mul` sets `q := 0` and drops its independent block, so `evalPoly` inherits that
contract: the independent block takes no part, and a caller who needs those
coefficients to count runs `dependent` once, on `S`, before evaluating.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Horner's rule, coordinatewise, coefficients lowest degree first: `[a₀]` is
the constant `a₀`, and `a₀ :: rest` is `a₀ + S * evalPoly rest`. -/
def PolyZonotope.evalPoly (S : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) := (PolyZonotope.evalPolyP S coeffs).1

end CORALean.Real
