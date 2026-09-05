import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Theorems.EvalDifferentiable

/-!
# The sensitivity is the derivative, wherever there is one

What makes `NeuralNetwork.sensitivity` a heuristic worth trusting rather than an
arbitrary weighting: on a chain differentiable layer by layer it is exactly
`fderiv ℝ nn.eval x` read as a matrix. The proof is `fderiv_comp` once per
layer, so the theorem is the chain rule and the definition is its computation.

`DifferentiableChain` and not `DifferentiableAt ℝ nn.eval x`, which would not
do: it is each factor's derivative that has to exist, since it is their product
being identified.

Nothing downstream depends on this. An enclosure is sound whatever the
sensitivity says, and a ReLU network — where the hypothesis fails at every zero
coordinate — is refined by the same numbers, which is the reason to leave the
definition unconditional and prove the agreement separately.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

theorem NeuralNetwork.sensitivity_eq_fderiv : ∀ {n m : ℕ} (nn : NeuralNetwork S n m)
    (x : Vec ℝ n), nn.DifferentiableChain x → nn.sensitivity x
      = LinearMap.toMatrix' (fderiv ℝ nn.eval x : Vec ℝ n →L[ℝ] Vec ℝ m).toLinearMap
  | _, _, .nil, x, _ => by
      show (1 : Mat ℝ _ _) = _
      -- the empty chain evaluates by the identity, whose matrix is the unit
      rw [show (fderiv ℝ (NeuralNetwork.eval (S := S) .nil) x) = ContinuousLinearMap.id ℝ _ from
        (hasFDerivAt_id x).fderiv]
      exact LinearMap.toMatrix'_id.symm
  | _, _, .cons L rest, x, h => by
      obtain ⟨hL, hrest⟩ : DifferentiableAt ℝ L.eval x ∧ rest.DifferentiableChain (L.eval x) := h
      show rest.sensitivity (L.eval x) * L.sensitivity x = _
      rw [rest.sensitivity_eq_fderiv _ hrest, Layer.sensitivity, ← LinearMap.toMatrix'_comp]
      congr 1
      -- the matrix product the definition takes is the composition the chain rule gives
      rw [show (fderiv ℝ (NeuralNetwork.eval (.cons L rest)) x)
        = (fderiv ℝ rest.eval (L.eval x)).comp (fderiv ℝ L.eval x) from
        fderiv_comp x (rest.differentiableAt_eval _ hrest) hL]
      rfl

end CORALean.Real
