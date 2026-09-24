import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Theorems.Real.SigmoidMono
import CORALean.NN.Layers.Theorems.Real.SigmoidPos

/-!
# The exact derivative bracket's lower end

ℝ-only, the bracket being `σ` itself at the box's ends: `σ` rises with its argument and
`σ (-·)` falls, so each factor is smallest at one end.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidDerivLo_le {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDerivLo l u ≤ sigmoidDeriv t :=
  mul_le_mul (sigmoid_mono hl) (sigmoid_mono (neg_le_neg hu))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
