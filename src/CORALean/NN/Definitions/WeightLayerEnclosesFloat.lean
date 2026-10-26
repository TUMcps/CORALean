module

public import CORALean.NN.Definitions.WeightLayerFloat
public import CORALean.NN.Definitions.WeightLayer
public import CORALean.NN.Definitions.Basic

@[expose] public section

/-!
# A float layer stands for a real one
`WeightLayer.Encloses L L'`: the two layers are of one kind, the real weights lie in the float
boxes, and the stored enclosure of an activation encloses the real function (`EnclosesScalar`).

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

/-- The real layer is of the float layer's kind, with its weights in the float boxes and its
function enclosed. -/
def WeightLayer.Encloses : ∀ {n m : ℕ}, WeightLayer 𝕋 n m → CORALean.WeightLayer ℝ n m → Prop
  | _, _, .linear W b, .linear W' b' => W' ∈ W.construct ∧ b' ∈ b.construct
  | _, _, .elementwiseAffine s o, .elementwiseAffine s' o' => s' ∈ s.construct ∧ o' ∈ o.construct
  | _, _, .identity, .identity => True
  | _, _, .activation fE, .activation f => EnclosesScalar fE f
  | _, _, _, _ => False

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
