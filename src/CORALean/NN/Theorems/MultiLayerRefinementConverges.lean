module

public import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Definitions.SigmoidNetworks
public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ActivationPolyRefinable
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
public import CORALean.NN.Theorems.ActivationLipschitz
public import CORALean.NN.Theorems.EncloseAtInflate
public import CORALean.NN.Theorems.EvalLipschitz
public import CORALean.NN.Theorems.LinearLipschitz
public import CORALean.NN.Theorems.Real.LinearConvergent
public import CORALean.NN.Theorems.SigmoidLipschitz

@[expose] public section

/-!
# The network statement, at a network with three layers

`SigmoidRefinementConverges` discharges `Convergent` where the tail is empty and its Lipschitz
constant is `LipschitzWith.id`. Here neither is free: the head activation's residual passes through
a matrix and a second activation before it reaches the output, so the tail bound is a product of two
real constants and the `K` in `EncloseAtInflate` is what the refinement level is divided by. The
linear layer meets `Convergent` at every level, its propagation being exact, so the schedule spends
its levels on the two activations. This is [1, Thm. 4.14]'s hypothesis met where the tail is not
trivial.

## Inputs
* `W` – weight matrix
* `b` – bias vector

## Hypotheses
* none

## Conclusion
* the sigmoid, linear, sigmoid network is convergent

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidLinearSigmoidNetwork_convergent (W : Mat ℝ m n) (b : Vec ℝ m) : -- --- CONCL ---
    (Real.sigmoidLinearSigmoidNetwork W b).Convergent := by -- --- PROOF ---
  -- the last activation on its own, which is where the tail bound bottoms out
  have h₂ : (RefinableNetwork.cons (S := 𝒫𝒵)
      (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily
        Real.sigmoidPolyFamily_sound) .nil).LipschitzLayers :=
    ⟨⟨1, Layer.lipschitzWith_activation_eval lipschitzWith_sigmoid m⟩, trivial⟩
  -- and the matrix in front of it, whose constant is its largest row sum
  have h₁ : (RefinableNetwork.cons (S := 𝒫𝒵)
      ((Layer.linear W b).refinable (Layer.linear_encloses W b))
      (.cons (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily
        Real.sigmoidPolyFamily_sound)
        .nil)).LipschitzLayers :=
    ⟨⟨_, Layer.lipschitzWith_linear_eval W b⟩, h₂⟩
  exact ⟨Real.Layer.activationPolySigmoid_convergent n,
    RefinableNetwork.exists_lipschitzWith_eval _ h₁,
    Layer.linear_refinable_convergent W b,
    RefinableNetwork.exists_lipschitzWith_eval _ h₂,
    Real.Layer.activationPolySigmoid_convergent m, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
