module

public import CORALean.ContSet.ConZonotope.Float.Operations.Basic
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
public import CORALean.ContSet.Zonotope.Float.Operations.BallB
public import CORALean.ContSet.Zonotope.Float.Operations.Deviation

@[expose] public section

/-!
# `ConZonotope.containsPoint`, over a floating-point scalar

A point certified inside, by a coefficient point `β₀` and a right inverse `H` of the generator
matrix that the caller proposes: `ConZonotope.interiorCert` makes the box of radius `B` around
`y₀ = c + G β₀` part of the nominal set, and the point, moved by the error box's lower corner, is
checked to lie in it (`Zonotope.deviation`, rounded upward). No exact solve `G β = p - c` is
needed; the box absorbs the rounding. Sufficient only: `true` proves membership.

## Inputs
* `cZ` – float constrained zonotope
* `H` – right inverse of the generator matrix
* `β₀` – coefficient point
* `p` – point to test

## Output
* whether the point is certified inside
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.containsPoint (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (H : Mat 𝕋 cZ.h n) (β₀ : Vec 𝕋 cZ.h)
    (p : Vec 𝕋 n) : Bool :=
  let δ := cZ.interiorMargin β₀
  cZ.interiorCert H β₀ δ (Zonotope.ballB H δ)
    && le (Zonotope.deviation p cZ.I_error.inf (cZ.centerLo β₀) (cZ.centerHi β₀))
        (Zonotope.ballB H δ)
    && (List.finRange n).all fun i => le (cZ.I_error.inf i) (cZ.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
