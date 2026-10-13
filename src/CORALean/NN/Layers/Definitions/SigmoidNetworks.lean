import CORALean.NN.Definitions.RefinableNetwork
import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Layer
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Theorems.LinearSound
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
import CORALean.NN.Operations.LayerRefinable

/-!
# The refinable networks the convergence theorems are about

Three chains at the sigmoid family, over the exact polynomial zonotope: the activation alone,
the two-layer `σ(W x + b)` [1, Prop. 4.13] is stated on — the linear layer spends no level and
the activation all of them, the smallest chain in which refinement has anything to do — and
sigmoid, then `W x + b`, then sigmoid, the smallest in which every part of the loop is doing
work, the first activation's residual surviving both layers after it. The weights are
arbitrary, so each is a family and not an example.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sigmoid layer as a network, named so the statements about it stay readable. -/
noncomputable def sigmoidRefinableNetwork (n : ℕ) : RefinableNetwork 𝒫𝒵 n n :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_sound) .nil

/-- A linear layer, which takes every level as itself, and the refinable activation behind it. -/
noncomputable def linearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons ((CORALean.Layer.linear W b).refinable (CORALean.Layer.linear_sound W b))
    (.cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_sound) .nil)

/-- Two refinable activations around a linear layer, which has nothing to spend. -/
noncomputable def sigmoidLinearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_sound)
    (.cons ((CORALean.Layer.linear W b).refinable (CORALean.Layer.linear_sound W b))
      (.cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_sound) .nil))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
