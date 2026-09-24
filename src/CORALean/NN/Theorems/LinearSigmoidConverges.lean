import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidNetworks
import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.ActivationPolyRefinable
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
import CORALean.NN.Operations.NetworkConvergent
import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.Real.LinearConvergent
import CORALean.NN.Theorems.SigmoidLipschitz

/-!
# The two-layer network is convergent

[1, Prop. 4.13]'s hypothesis, discharged: the linear layer meets `Convergent` at
every level because its propagation is exact, and the activation meets it by
raising the order of its fit, so every level the schedule buys is spent where the
approximation error is.

The tail bound the network statement asks for is free on both sides here. Behind
the linear layer the tail is one sigmoid, whose constant is `1`; behind the
activation the tail is empty. So no residual is amplified anywhere, which is why
this case needs none of the care `MultiLayerRefinementConverges` does.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem linearSigmoidNetwork_convergent (W : Mat ℝ m n) (b : Vec ℝ m) :
    (Real.linearSigmoidNetwork W b).Convergent := by -- --- PROOF ---
  -- the activation on its own, which is the whole tail behind the matrix
  have h : (RefinableNetwork.cons (S := 𝒫𝒵)
      (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily
        Real.sigmoidPolyFamily_sound) .nil).LipschitzLayers :=
    ⟨⟨1, Layer.lipschitzWith_activation_eval lipschitzWith_sigmoid m⟩, trivial⟩
  exact ⟨Layer.linear_refinable_convergent W b,
    RefinableNetwork.exists_lipschitzWith_eval _ h,
    Real.Layer.activationPolySigmoid_convergent m, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
