module

public import CORALean.NN.Layers.Definitions.PolyFamily
public import CORALean.NN.Layers.Theorems.Real.AbsSigmoidDerivLeOne
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid

@[expose] public section

/-!
# The refinement loop's family at the sigmoid

`polyRelaxationFamily` asks for a derivative and a bound on it over all of ℝ, and the sigmoid
has both, `σ'` being a product of two sigmoids each inside `(0,1)`. CORA's `nn.refine` at the
sigmoid [1], with the choice of fit left open. Over ℝ, as the family is.

## Inputs
* none

## Output
* family of polynomial relaxations of the sigmoid

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Level `o` fits the sigmoid on `[-o, o]` to within `1 / (o + 1)`. -/
noncomputable def sigmoidPolyFamily : PolyRelaxationFamily ℝ :=
  polyRelaxationFamily hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
