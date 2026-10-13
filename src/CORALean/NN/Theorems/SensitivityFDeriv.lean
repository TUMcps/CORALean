import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Theorems.EvalDifferentiable
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The sensitivity is the derivative, wherever there is one

What makes `Chain.sensitivity` a heuristic worth trusting rather than an
arbitrary weighting: on a chain differentiable layer by layer it is exactly
`fderiv ℝ c.eval x` read as a matrix. The proof is `fderiv_comp` once per
layer, so the theorem is the chain rule and the definition is its computation.

`DifferentiableChain` and not `DifferentiableAt ℝ c.eval x`, which would not
do: it is each factor's derivative that has to exist, since it is their product
being identified.

Nothing downstream depends on this. An enclosure is sound whatever the
sensitivity says, and a ReLU network — where the hypothesis fails at every zero
coordinate — is refined by the same numbers, which is the reason to leave the
definition unconditional and prove the agreement separately.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.sensitivity_eq_fderiv : ∀ {n m : ℕ} (c : Chain n m)
    (x : Vec ℝ n), c.DifferentiableChain x → c.sensitivity x
      = LinearMap.toMatrix' (fderiv ℝ c.eval x : Vec ℝ n →L[ℝ] Vec ℝ m).toLinearMap
  | _, _, .nil, x, _ => by
      show (1 : Mat ℝ _ _) = _
      -- the empty chain evaluates by the identity, whose matrix is the unit
      rw [show (fderiv ℝ (Chain.eval .nil) x) = ContinuousLinearMap.id ℝ _ from
        (hasFDerivAt_id x).fderiv]
      exact LinearMap.toMatrix'_id.symm
  | _, _, .cons f rest, x, h => by
      obtain ⟨hf, hrest⟩ : DifferentiableAt ℝ f x ∧ rest.DifferentiableChain (f x) := h
      show rest.sensitivity (f x) * layerSensitivity f x = _
      rw [rest.sensitivity_eq_fderiv _ hrest, layerSensitivity, ← LinearMap.toMatrix'_comp]
      congr 1
      -- the matrix product the definition takes is the composition the chain rule gives
      rw [show (fderiv ℝ (Chain.eval (.cons f rest)) x)
        = (fderiv ℝ rest.eval (f x)).comp (fderiv ℝ f x) from
        fderiv_comp x (rest.differentiableAt_eval _ hrest) hf]
      rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
