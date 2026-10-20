module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# `convertTransitionMatrix` keeps the columns stochastic

The block-diagonal matrix of column-stochastic matrices is column-stochastic.

## Inputs
* `N` – cell count
* `Phi` – transition matrix per input

## Hypotheses
* `h` – each matrix is column-stochastic

## Conclusion
* the combined matrix is column-stochastic
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

/-- The matrix `aux_convert` builds is column-stochastic if every `Phi i` is. -/
theorem MarkovChain.convertT_mem {N : ℕ} (Phi : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : ∀ i, Phi i ∈ Matrix.colStochastic ℝ (Fin (N + 1))) : -- --- CONCL ---
    MarkovChain.convertT Phi ∈ Matrix.colStochastic ℝ (Fin (N + 1) × Fin m) := by -- --- PROOF ---
  rw [Matrix.mem_colStochastic_iff_sum]
  refine ⟨fun a b => ?_, fun b => ?_⟩
  · unfold MarkovChain.convertT
    split_ifs
    · exact Matrix.nonneg_of_mem_colStochastic (h _)
    · exact le_rfl
  · -- only the rows of the column's own input are nonzero
    unfold MarkovChain.convertT
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single b.2]
    · simp only [if_true]
      exact Matrix.sum_col_of_mem_colStochastic (h b.2) b.1
    · intro i _ hi
      simp [hi]
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
