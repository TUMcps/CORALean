module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi

@[expose] public section

/-!
# The Krylov basis of the Arnoldi iteration

The matrix `V` of [1, Alg. 1] after `ξ` passes: its columns `v⁽¹⁾, …, v⁽ξ⁾` (indices
`0, …, ξ - 1`) are the first `ξ` vectors `arnoldi` stores, and `v⁽ξ⁺¹⁾`, the one the residual
`h_{ξ+1,ξ} v⁽ξ⁺¹⁾` of the Arnoldi relation points along, is left out, as [1]'s (1) leaves it out.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `V = [v⁽¹⁾, …, v⁽ξ⁾]`, column `k` the vector `arnoldi` stores at index `k`. -/
noncomputable def Krylov.arnoldiBasis (C : Mat ℝ n n) (v : Vec ℝ n) (ξ : ℕ) : Mat ℝ n ξ :=
  Matrix.of fun i k => (Krylov.arnoldi C v ξ).1 k i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
