module

public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The chord-tangent relaxation of the square

The band of `x ↦ x²` over `[l, u]` between the chord (slope `s = l + u`) and the parallel tangent:
`x² - s x` runs from `-m²` at `m = s / 2` to `-l u` at the ends, so the offset is `-(l u + m²) / 2`
and the radius `(u - l)² / 8`, an eighth of `squareRelaxation`'s. CORA.cpp's `priv_square_line`,
in its order, with its margin `w · max(l², u²)`. The rounding of the slope and the offset adds the
spread `Δ` of `l + u` times `2 max(|l|, |u|) + Δ` and the offset's distance to its upper rounding:
differences of one value rounded two ways, zero at round to nearest, where it is CORA.cpp's.

## Inputs
* `w` – the rounding margin's factor (CORA.cpp's `8 eps`)

## Output
* the chord-tangent relaxation of the square
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `l u + m²` rounded up, `m` the middle of the box. -/
@[step_of squareChordTangentRelaxation]
def step_squareChordSumUp (l u : 𝕋) : 𝕋 :=
  let m := half (addUp l u)
  addUp (mulUp l u) (mulUp m m)

/-- `l u + m²` rounded down. -/
@[step_of squareChordTangentRelaxation]
def step_squareChordSumDown (l u : 𝕋) : 𝕋 :=
  let m := half (addUp l u)
  addDown (mulDown l u) (mulDown m m)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band between the chord and the parallel tangent, widened by the margin and the rounding
of the slope and the offset. -/
def squareChordTangentRelaxation (w : 𝕋) : Relaxation 𝕋 where
  slope l u := addUp l u
  offset l u := half (neg (step_squareChordSumUp l u))
  error l u :=
    -- the radius (u - l)² / 8 and the margin w max(l², u²)
    let d := subUp u l
    let radius := mulUp (mulUp d d) (half (half (half one)))
    let margin := mulUp (maximum (mulUp l l) (mulUp u u)) w
    -- the slope's rounding: its spread times 2 max(|l|, |u|) plus the spread
    let spread := subUp (addUp l u) (addDown l u)
    let k := maximum (absolute l) (absolute u)
    let slopeCost := mulUp spread (addUp (addUp k k) spread)
    -- the offset's rounding: up to the other end of -(l u + m²) / 2
    let offsetCost :=
      subUp (half (neg (step_squareChordSumDown l u))) (half (neg (step_squareChordSumUp l u)))
    addUp (addUp (addUp radius margin) slopeCost) offsetCost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
