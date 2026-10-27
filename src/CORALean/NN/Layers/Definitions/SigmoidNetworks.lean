module

public import CORALean.NN.Definitions.RefinableNetwork
public import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
public import CORALean.NN.Operations.LayerRefinable

@[expose] public section

/-!
# The refinable networks the convergence theorems are about

Three chains at the sigmoid family, over the exact polynomial zonotope: the activation alone,
the two-layer `σ(W x + b)` [1, Prop. 4.13] is stated on — the linear layer spends no level and
the activation all of them, the smallest chain in which refinement has anything to do — and
sigmoid, then `W x + b`, then sigmoid, the smallest in which every part of the loop is doing
work, the first activation's residual surviving both layers after it. The weights are
arbitrary, so each is a family and not an example.

## Inputs
* `n` – layer width

## Output
* refinable network made of one sigmoid layer

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sigmoid layer as a network, named so the statements about it stay readable. Noncomputable
because the sigmoid's polynomial relaxation family is built from the real sigmoid. -/
noncomputable def sigmoidRefinableNetwork (n : ℕ) : RefinableNetwork 𝒫𝒵 n n :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_isSound) .nil

/-- A linear layer, which takes every level as itself, and the refinable activation behind it. -/
noncomputable def linearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons ((CORALean.Layer.linear W b).refinable (CORALean.Layer.linear_encloses W b))
    (.cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_isSound) .nil)

/-- Two refinable activations around a linear layer, which has nothing to spend. -/
noncomputable def sigmoidLinearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_isSound)
    (.cons ((CORALean.Layer.linear W b).refinable (CORALean.Layer.linear_encloses W b))
      (.cons (Layer.activationPolyRefinable sigmoidPolyFamily sigmoidPolyFamily_isSound) .nil))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
