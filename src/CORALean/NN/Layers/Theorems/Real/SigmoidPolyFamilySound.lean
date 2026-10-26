module

public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilySound

@[expose] public section

/-!
# The sigmoid family is sound

ℝ-only, as the family is: every level a sampled relaxation of the sigmoid.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the family is sound for the sigmoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidPolyFamily_isSound : sigmoidPolyFamily.IsSound sigmoid :=
  polyRelaxationFamily_isSound hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
