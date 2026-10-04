import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-!
# A weighted square as a trace

`tr(W v vᵀ) = vᵀ W v`: the step from a weighted Frobenius norm, a sum of `gᵀ W g` over the
generators `g`, to the trace of `W` against `Σ g gᵀ`, in which the gain-optimality proofs of
the zonotopic Kalman observers are written.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
