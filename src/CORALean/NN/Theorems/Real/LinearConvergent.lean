module

public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Operations.IsConvergent
public import CORALean.NN.Operations.LayerRefinable
public import CORALean.NN.Theorems.Real.LinearExact

@[expose] public section

/-!
# The linear layer converges, at every level

ℝ-only, resting on `Real.Layer.linear_exact`: at a machine scalar the enclosure pays rounding.
`Layer.refinable` puts a layer with nothing to spend into a refinable network, and `IsConvergent`
then has to be met by its single enclosure. It is, because that enclosure is exact: any order
pattern already lands the enclosed set on the image. So the linear layer contributes no residual to
`EncloseAtInflate`'s budget, and everything the schedule buys is bought at the activations. That is
where [1, Prop. 4.13]'s proof starts — "the linear layer is computed exactly".

## Inputs
* `W` – weight matrix
* `b` – bias vector

## Hypotheses
* none

## Conclusion
* the linear layer as a refinable layer is convergent

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- ℝ-only, the linear layer being exact at the polynomial zonotope only there. -/
theorem Layer.linear_refinable_convergent (W : Mat ℝ m n) (b : Vec ℝ m) : -- --- CONCL ---
    ((CORALean.Layer.linear (S := 𝒫𝒵) W b).refinable
      (CORALean.Layer.linear_encloses W b)).IsConvergent := by -- --- PROOF ---
  intro s ε hε
  refine ⟨fun _ => 0, ?_⟩
  show construct ((CORALean.Layer.linear (S := 𝒫𝒵) W b).enclose s)
      ⊆ (fun x => W *ᵥ x + b) '' construct s + Metric.closedBall 0 ε
  rw [Layer.linear_exact]
  intro y hy
  -- the enclosed set is the image already, so the ball contributes zero
  have h0 : (0 : Vec ℝ m) ∈ Metric.closedBall (0 : Vec ℝ m) ε := by
    rw [Metric.mem_closedBall, dist_self]
    exact hε.le
  have hmem := Set.add_mem_add hy h0
  rwa [add_zero] at hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
