module

public import CORALean.NN.Layers.Operations.ClampUnit

@[expose] public section

/-!
# `crownReluLines`

CROWN's two lines of a ReLU on the box `[l, u]`, as CORA.cpp's backward bound takes them
(`priv_backward_lower`): the identity where `0 ≤ l`, zero where `u ≤ 0`, and where the box crosses
zero the line `a t` below (`a` the optimized slope `alpha`, clamped into `[0, 1]`, else CROWN's
`1` where `u > -l` and `0` otherwise) and the chord's slope `s = u / (u - l)` above, raised to the
larger of `relu(l) - s l` and `relu(u) - s u`, the two ends of the convex `relu(t) - s t`. CORA.cpp
takes `-s l` alone, which the rounded `s` can leave below `relu(u) - s u`.

## Inputs
* `alpha` – the optimized lower slope, if any
* `l` – lower bound of the input
* `u` – upper bound of the input

## Output
* the lower slope and offset, then the upper slope and offset
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def crownReluLines (alpha : Option 𝕋) (l u : 𝕋) : 𝕋 × 𝕋 × 𝕋 × 𝕋 :=
  -- 1. the box on one side of zero: the identity, or zero
  if le zero l then (one, zero, one, zero)
  else if le u zero then (zero, zero, zero, zero)
  else
    -- 2. below: the slope `a` through the origin
    let a := match alpha with
      | some a => clampUnit a
      | none => if ltStrict (neg l) u then one else zero
    -- 3. above: the chord's slope, raised over both ends of the box
    let s := divDown u (subUp u l)
    let bu := maximum (subUp (maximum l zero) (mulDown s l)) (subUp (maximum u zero) (mulDown s u))
    (a, zero, s, bu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
