module

public import CORALean.NN.Layers.Operations.ConjError

@[expose] public section

/-!
# A relaxation carried along an affine conjugation

`g t = ra f (rb t) + c`, `ra, rb > 0`, inherits `f`'s relaxation, read at the box `rb` maps
`[l, u]` to and rescaled: tanh is sigmoid's this way, `a = b = 2`, `c = -1`. The price for
storing one slope rather than the exact product is the gap between its two roundings, charged
against a bound on `t` itself; at exact scalings there is none.

## Inputs
* `R` – relaxation of the activation
* `A` – rounding of the output scale
* `B` – rounding of the input scale
* `c` – output shift

## Output
* relaxation of the conjugated activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g t = ra f (rb t) + c` inherits `f`'s relaxation. -/
def Relaxation.ofAffineConj (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (c : 𝕋) :
    Relaxation 𝕋 where
  slope := Relaxation.conjSlope R A B
  offset := Relaxation.conjOffset R A B c
  error := Relaxation.conjError R A B c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
