module

public import CORALean.DiscrDynamics.MarkovChain.Theorems.GammaMem
public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# `GammaFull` is column-stochastic

A block `Gamma` for each cell keeps every column a distribution.

## Inputs
* `N` – cell count
* `m` – number of inputs
* `γ` – input mixing parameter

## Hypotheses
* `hγ` – mixing parameter positive

## Conclusion
* the block mixing matrix is column-stochastic
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `γ > 0`, `GammaFull` is column-stochastic. -/
theorem MarkovChain.gammaFull_mem (N m : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    MarkovChain.gammaFull N m γ ∈ Matrix.colStochastic ℝ (Fin (N + 1) × Fin m)
      := by -- --- PROOF ---
  have h := MarkovChain.gamma_mem m hγ
  rw [Matrix.mem_colStochastic_iff_sum] at h ⊢
  refine ⟨fun a b => ?_, fun b => ?_⟩
  · unfold MarkovChain.gammaFull; split_ifs
    · exact h.1 _ _
    · exact le_rfl
  · -- one block of the column is nonzero
    unfold MarkovChain.gammaFull
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b.1]
    · simp only [if_true]; exact h.2 b.2
    · intro s _ hs; simp [hs]
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
