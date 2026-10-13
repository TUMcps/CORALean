import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilySound

/-!
# The sigmoid family is sound

ℝ-only, as the family is: every level a sampled relaxation of the sigmoid.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidPolyFamily_sound : sigmoidPolyFamily.Sound sigmoid :=
  polyRelaxationFamily_sound hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
