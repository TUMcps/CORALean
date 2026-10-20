module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Gamma

@[expose] public section

/-!
# `Gamma` is column-stochastic

With `γ > 0` the weights `1 / ((i - j)² + γ)` are positive, so the normalization divides by a
positive sum and every column adds up to one.

## Inputs
* `m` – number of inputs
* `γ` – input mixing parameter

## Hypotheses
* `hγ` – mixing parameter positive

## Conclusion
* the mixing matrix is column-stochastic
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `γ > 0` the normalized input weights are column-stochastic. -/
theorem MarkovChain.gamma_mem (m : ℕ) {γ : ℝ} (hγ : 0 < γ) : -- --- CONCL ---
    MarkovChain.gamma m γ ∈ Matrix.colStochastic ℝ (Fin m) := by -- --- PROOF ---
  rw [Matrix.mem_colStochastic_iff_sum]
  have hg : ∀ a b : Fin m, 0 < 1 / (((a : ℕ) - (b : ℕ) : ℝ) ^ 2 + γ) := fun a b => by positivity
  have hs : ∀ j : Fin m, 0 < ∑ k : Fin m, 1 / (((k : ℕ) - (j : ℕ) : ℝ) ^ 2 + γ) := fun j =>
    Finset.sum_pos (fun k _ => hg k j) ⟨j, Finset.mem_univ _⟩
  refine ⟨fun i j => ?_, fun j => ?_⟩
  · unfold MarkovChain.gamma; dsimp only; split_ifs
    · exact (div_pos (hg i j) (hs j)).le
    · exact (hg i j).le
  · -- the column sum is the normalizer over itself
    unfold MarkovChain.gamma
    dsimp only
    simp only [(hs j).ne', ne_eq, not_false_eq_true, if_true]
    rw [← Finset.sum_div, div_self (hs j).ne']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
