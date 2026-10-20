module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A weighted square as a trace

`tr(W v vᵀ) = vᵀ W v`: the step from a weighted Frobenius norm, a sum of `gᵀ W g` over the
generators `g`, to the trace of `W` against `Σ g gᵀ`, in which the gain-optimality proofs of
the zonotopic Kalman observers are written.

## Inputs
* `W` – weight matrix
* `v` – vector

## Hypotheses
* none

## Conclusion
* the weighted trace of the outer square is the weighted quadratic form
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem trace_mul_vecMulVec_self (W : Mat ℝ n n) (v : Vec ℝ n) :
    trace (W * vecMulVec v v) = v ⬝ᵥ (W *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
