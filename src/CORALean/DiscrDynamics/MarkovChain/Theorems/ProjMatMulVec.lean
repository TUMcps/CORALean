module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# `projMat` sums over the inputs

Multiplying a distribution over (cell, input) by `projMat` gives the cell marginal.

## Inputs
* `N` – cell count
* `m` – number of inputs
* `p` – distribution over cells and inputs
* `s` – cell

## Hypotheses
* none

## Conclusion
* the projection gives the cell marginal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `projMat p` at cell `s` is the sum of `p (s, i)` over the inputs `i`. -/
theorem MarkovChain.projMat_mulVec (N m : ℕ) (p : Fin (N + 1) × Fin m → ℝ) (s : Fin (N + 1)) :
    (MarkovChain.projMat N m *ᵥ p) s = ∑ i, p (s, i) := by -- --- PROOF ---
  unfold MarkovChain.projMat Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
