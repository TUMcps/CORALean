import CORALean.NN.Layers.SigmoidLinearSigmoid
import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.LinearConvergent
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.EncloseAtInflate
import CORALean.NN.Theorems.SigmoidLipschitz

/-!
# The network statement, at a network with three layers

`SigmoidRefinementConverges` discharges `Convergent` where the tail is empty and
its Lipschitz constant is `LipschitzWith.id`. Here neither is free: the head
activation's residual passes through a matrix and a second activation before it
reaches the output, so the tail bound is a product of two real constants and the
`K` in `EncloseAtInflate` is what the refinement level is divided by.

The linear layer meets `Convergent` at level `0` and every other level, its
propagation being exact — so the schedule spends its levels on the two
activations, and the middle layer only rescales what they leave — the division
of labour the loop assumes [1].

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidLinearSigmoidNetwork_convergent (W : Mat ℝ m n) (b : Vec ℝ m) :
    (Real.sigmoidLinearSigmoidNetwork W b).Convergent := by -- --- PROOF ---
  -- the last activation on its own, which is where the tail bound bottoms out
  have h₂ : (RefinableNetwork.cons (S := 𝒫𝒵)
      (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily) .nil).LipschitzLayers :=
    ⟨⟨1, Layer.lipschitzWith_activation_eval lipschitzWith_sigmoid m⟩, trivial⟩
  -- and the matrix in front of it, whose constant is its largest row sum
  have h₁ : (RefinableNetwork.cons (S := 𝒫𝒵)
      ((Real.Layer.linear W b).refinable (Real.Layer.linear_sound W b))
      (.cons (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily)
        .nil)).LipschitzLayers :=
    ⟨⟨_, Layer.lipschitzWith_linear_eval W b⟩, h₂⟩
  exact ⟨Real.Layer.activationPolySigmoid_convergent n,
    RefinableNetwork.exists_lipschitzWith_eval _ h₁,
    Layer.linear_refinable_convergent W b,
    RefinableNetwork.exists_lipschitzWith_eval _ h₂,
    Real.Layer.activationPolySigmoid_convergent m, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
