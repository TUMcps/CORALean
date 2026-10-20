module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.representsa_point`, over a floating-point scalar

CORA's `@polyZonotope/representsa_` at type `point`, tolerance `0`: every dependent and independent
generator entry is `0` and the error box is a single point; `le` answers only `true` reliably, so a
`true` is sound and a `false` decides nothing.

## Inputs
* `pZ` – polynomial zonotope

## Output
* Boolean, true only if all generators and the error box vanish
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

def PolyZonotope.representsa_point (pZ : PolyZonotope (Vec 𝕋 n)) : Bool :=
  (((List.finRange pZ.h).all fun j => (List.finRange n).all fun i =>
    FloatOps.le (pZ.G j i) zero && FloatOps.le zero (pZ.G j i)) &&
    ((List.finRange pZ.q).all fun j => (List.finRange n).all fun i =>
      FloatOps.le (pZ.GI j i) zero && FloatOps.le zero (pZ.GI j i)) &&
    pZ.I_error.representsa_point)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
