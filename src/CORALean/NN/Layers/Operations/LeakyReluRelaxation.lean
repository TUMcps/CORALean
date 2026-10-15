module

public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# The leaky ReLU relaxation

`max(α t, t)` is convex for `α ≤ 1`, so it lies above any line through the origin of slope in
`[α, 1]` and below it raised by the larger of its two end values: the relaxation of CORA's
`nnLeakyReLULayer` for a stored `α` and a chosen slope `lam`, clamped into `[α, 1]` as ReLU's is
into `[0, 1]`. Recentered, so the error is half the gap.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Recentered, so that the error is half the gap in each direction. -/
def leakyReluRelaxation (α : 𝕋) (lam : 𝕋 → 𝕋 → 𝕋) : Relaxation 𝕋 where
  slope l u := maximum α (minimum one (lam l u))
  offset l u := half (leakyReluGapUp α (maximum α (minimum one (lam l u))) l u)
  error l u := half (leakyReluGapUp α (maximum α (minimum one (lam l u))) l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
