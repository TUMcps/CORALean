module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# `Global`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open Matrix


-- ===============================  `trace_transpose_mul_eq_sum`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`. -/
theorem trace_transpose_mul_eq_sum {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) :
    trace (Aᵀ * B) = ∑ k, ∑ j, A k j * B k j := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
