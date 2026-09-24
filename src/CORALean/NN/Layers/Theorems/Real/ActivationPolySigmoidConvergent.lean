import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Theorems.Real.ActivationPolyRefinableConvergent
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound

/-!
# The sigmoid activation layer converges under refinement

ℝ-only, as convergence is: the nonlinear half of [1, Prop. 4.13], at a layer someone would
actually build.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPolySigmoid_convergent (n : ℕ) :
    (Layer.activationPolyRefinable (n := n) sigmoidPolyFamily sigmoidPolyFamily_sound).Convergent :=
  Layer.activationPolyRefinable_convergent hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
