import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidNetworks
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
import CORALean.NN.Theorems.EncloseAtInflate

/-!
# The network statement, at a network that exists

`EncloseAtInflate` runs on a hypothesis — every layer convergent, every tail
Lipschitz — and a hypothesis is worth only what satisfies it. This discharges it
at a sigmoid layer, so the schedule it produces is one an implementation could
be asked for.

The tail is empty and its `eval` is the identity, which is where the Lipschitz
constant comes from. That is the easy case of the hypothesis, and deliberately
so: the point being made is that the *layer* half is met at a real activation,
`Layer.activationPolySigmoid_convergent` being the part with content.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRefinableNetwork_convergent (n : ℕ) : (Real.sigmoidRefinableNetwork n).Convergent :=
  ⟨Real.Layer.activationPolySigmoid_convergent n, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
