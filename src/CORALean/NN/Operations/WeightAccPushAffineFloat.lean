module

public import CORALean.NN.Definitions.WeightAccFloat
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `WeightAcc.pushAffine` in floats
CORA's `W = diag(scale) * W; b = scale .* b + offset` on boxes: the diagonal box of the scale
(its stored diagonal blocks) times the weight box by `Interval.matMul`, the entrywise product of
the scale and the offset box by `Interval.times`, plus the layer's offset. Nothing fused yet
starts from the diagonal and the offset.

## Inputs
* none

## Output
* float accumulator after the elementwise affine layer
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def WeightAcc.pushAffine :
    WeightAcc 𝕋 n d → Interval (Vec 𝕋 d) → Interval (Vec 𝕋 d) → WeightAcc 𝕋 n d
  | .id, s, o => .aff ⟨diagonalBlock s.inf, diagonalBlock s.sup⟩ o
  | .aff W b, s, o =>
    .aff (Interval.matMul ⟨diagonalBlock s.inf, diagonalBlock s.sup⟩ W)
      (Interval.plus (Interval.times s b) o)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
