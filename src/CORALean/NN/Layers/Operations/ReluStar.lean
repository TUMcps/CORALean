module

public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.StarSetReluNeuron
public import CORALean.ContSet.StarSet.Real.Operations.RowBounds

@[expose] public section

/-!
# The ReLU layer on a star set

CORA's `nnActivationLayer/evaluateConZonotope`, which for the ReLU layer loops
`evaluateConZonotopeNeuron` over the neurons `1, …, n` (the other activations throw): per
neuron, the bounds from the current set, then the step. The bounds are read off the set the
earlier neurons have left, which is what CORA's loop does: its `c, G, l_, u_` are overwritten in
place.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Layer.reluStar (n : ℕ) : Layer (Real.StarSet Real.StarSet.LinPred) n n where
  enclose s := (List.finRange n).foldl (fun t j => t.reluNeuron j (t.rowBounds j)) s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
