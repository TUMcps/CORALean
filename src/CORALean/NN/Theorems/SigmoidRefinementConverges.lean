module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Definitions.SigmoidNetworks
public import CORALean.NN.Layers.Definitions.SigmoidRelaxation
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.Sigmoid
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
public import CORALean.NN.Theorems.EncloseAtInflate

@[expose] public section

/-!
# The network statement, at a network that exists

`EncloseAtInflate` runs on a hypothesis — every layer convergent, every tail Lipschitz — and a
hypothesis is worth only what satisfies it. This discharges it at a sigmoid layer, so the schedule
it produces is one an implementation could be asked for. The tail is empty and its `eval` is the
identity, which is where the Lipschitz constant comes from: the easy case of the hypothesis,
deliberately, since the point is that the *layer* half is met at a real activation,
`Layer.activationPolySigmoid_convergent` being the part with content.

## Inputs
* `n` – layer width

## Hypotheses
* none

## Conclusion
* the sigmoid network is convergent
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRefinableNetwork_convergent (n : ℕ) : (Real.sigmoidRefinableNetwork n).Convergent :=
  ⟨Real.Layer.activationPolySigmoid_convergent n, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
