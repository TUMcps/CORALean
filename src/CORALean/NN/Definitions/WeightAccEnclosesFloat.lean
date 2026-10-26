module

public import CORALean.NN.Definitions.WeightAccFloat
public import CORALean.NN.Definitions.WeightAcc
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# A float accumulator stands for a real one
`WeightAcc.Encloses A A'`: both nothing fused, or both a fused map with the real weights in the
float boxes.

## Inputs
* none

## Output
* the statement that the float one encloses the real one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The real accumulator is the float one's kind, its weights in the float boxes. -/
def WeightAcc.Encloses : ∀ {n d : ℕ}, WeightAcc 𝕋 n d → CORALean.WeightAcc ℝ n d → Prop
  | _, _, .id, .id => True
  | _, _, .aff W b, .aff W' b' => W' ∈ W.construct ∧ b' ∈ b.construct
  | _, _, _, _ => False

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
