module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The trace of `Aᵀ B` as an entrywise sum

`tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`. -/
theorem trace_transpose_mul_eq_sum {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) :
    trace (Aᵀ * B) = ∑ k, ∑ j, A k j * B k j := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
