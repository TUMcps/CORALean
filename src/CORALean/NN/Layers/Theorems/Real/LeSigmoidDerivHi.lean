module

public import CORALean.NN.Layers.Definitions.SigmoidRelaxation
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono
public import CORALean.NN.Layers.Theorems.Real.SigmoidPos

@[expose] public section

/-!
# The exact derivative bracket's upper end

ℝ-only, as `sigmoidDerivLo_le` is: each factor largest at its other end.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_sigmoidDerivHi {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDeriv t ≤ sigmoidDerivHi l u :=
  mul_le_mul (sigmoid_mono hu) (sigmoid_mono (neg_le_neg hl))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
