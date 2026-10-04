import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# The dynamic mode decomposition at a rank

CORA's `aux_dynamicModeDecomposition` of `identify`: with the economy SVD `X1 = V S Wᵀ`,
the candidate of rank `k` is `X2 W_k S_k⁻¹ V_kᵀ`, the first `k` singular triples. Written
with the triples past `k` zeroed, so one square factor serves every rank. The SVD itself is
an argument (a factorization, not a computation, and not unique); `X1` and `X2` the
snapshots and their successors.
The source is [1].

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p N r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X2 W_k diag(1 ./ diag(S_k)) V_kᵀ`, by the factors `V`, `s`, `W` of `X1`. -/
noncomputable def dmdCandidate (X2 : Mat ℝ n N) (V : Mat ℝ p r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) (k : ℕ) : Mat ℝ n p :=
  X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < k then (s i)⁻¹ else 0) * Vᵀ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
