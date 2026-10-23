module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The square root's relaxation over ℝ

The square root is monotone, so `Relaxation.ofMonotone` at its own values gives CORA's `nnRootLayer`
relaxation: the range over the box at slope zero. A specification, as the exact sigmoid and tanh
relaxations are.

## Inputs
* none

## Output
* relaxation of the square root by its range at slope zero
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The range of `Real.sqrt` over the box, at slope zero. -/
noncomputable def rootRelaxation : Relaxation ℝ := Relaxation.ofMonotone (Enclosure.exact Real.sqrt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
