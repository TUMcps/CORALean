import CORALean.ContDynamics.OutputEq.OutputEq

/-!
# The parameters of a general output model

CORA's `p_GO` of `linearSysDT/computeGO` [1], for the `nk` steps `0, …, nk-1`: `A k` and
`B k j` give the state `x(k+1)` from the initial state and the input `u(j)`; `C k` and `D k j`
give the output `y(k)` the same way. Entries with `j` past `k` are zero. Not kept: CORA's
`F` and `E`, which carry the linearization error of the nonlinear case, and the reference
signals `x`, `y`, `u`.

## References

* [1] `contDynamics/@linearSysDT/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.GO (n r nk : ℕ) where
  A : Fin nk → Mat ℝ n n
  B : Fin nk → Fin nk → Mat ℝ n n
  C : Fin nk → Mat ℝ r n
  D : Fin nk → Fin nk → Mat ℝ r n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
