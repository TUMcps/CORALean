module

public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# A relaxation from a band of `σ - s x`

CORA.cpp's lines in its own form: a slope `s`, a lower end `lo` and an upper end `hi` of
`σ(x) - s x` on the box, and a margin `b`. The offset is the middle `(hi + lo) / 2` rounded down,
the error half the width `(hi - lo) / 2` plus the margin, and plus half the spread of `hi + lo`
between its two roundings, which the middle's rounding costs: zero at round to nearest, where
the error is CORA.cpp's `(hi - lo) * 0.5 + b`.

## Inputs
* `s` – the slope on a box
* `lo` – the band's lower end on a box
* `hi` – the band's upper end on a box
* `b` – the margin on a box

## Output
* the relaxation of slope `s` at the band's middle
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band's middle, half its width plus the middle's rounding, and the margin. -/
def Relaxation.ofBand (s lo hi b : 𝕋 → 𝕋 → 𝕋) : Relaxation 𝕋 where
  slope := s
  offset l u := half (addDown (hi l u) (lo l u))
  error l u :=
    let width := half (subUp (hi l u) (lo l u))
    let spread := half (subUp (addUp (hi l u) (lo l u)) (addDown (hi l u) (lo l u)))
    addUp (addUp width spread) (b l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
