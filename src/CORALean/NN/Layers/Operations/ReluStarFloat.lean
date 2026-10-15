module

public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.StarSetFloatReluNeuron
public import CORALean.ContSet.StarSet.Float.Operations.RowBounds

@[expose] public section

/-!
# The ReLU layer on a float star set

`Layer.reluStar` on a star set stored in `𝕋`: per neuron, the bounds from the set the earlier
neurons left, then the step. The bounds are the certified `Float.StarSet.rowBounds`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `evaluateConZonotope` for the ReLU layer, on a float star set. -/
def Layer.reluStarFloat (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (n : ℕ) :
    Layer (fun n => Float.StarSet 𝕋 n) n n where
  enclose s := (List.finRange n).foldl (fun t j => t.reluNeuron j (t.rowBounds j)) s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
