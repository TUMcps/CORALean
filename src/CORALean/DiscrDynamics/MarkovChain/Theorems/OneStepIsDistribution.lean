module

public import CORALean.DiscrDynamics.MarkovChain.Definitions.Basic

@[expose] public section

/-!
# A stochastic chain moves distributions to distributions

What makes a `MarkovChain` a Markov chain: a column-stochastic transition matrix sends a
probability vector over the cells (the outside first) to another.

## Inputs
* `M` – Markov chain
* `i` – input index
* `p` – distribution over the cells

## Hypotheses
* `h` – chain is stochastic
* `hp0` – entries nonnegative
* `hp1` – entries sum to one

## Conclusion
* the step image is a distribution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `T.T i` column-stochastic, a distribution over the cells stays one after a step. -/
theorem MarkovChain.oneStep_isDistribution (M : MarkovChain n m) (h : M.IsStochastic) (i : Fin m)
    {p : Fin (M.field.nrOfCells + 1) → ℝ} (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) :
    (∀ s, 0 ≤ (M.T.T i *ᵥ p) s) ∧ ∑ s, (M.T.T i *ᵥ p) s = 1 := by
  refine ⟨fun s => Matrix.nonneg_mulVec_of_mem_colStochastic (h i).1 hp0 s, ?_⟩
  rw [Matrix.sum_mulVec_of_mem_colStochastic (h i).1, hp1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
