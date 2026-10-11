import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi

/-!
# The Hessenberg matrix of the Arnoldi iteration

The `ξ × ξ` matrix `H` of [1, Alg. 1] after `ξ` passes, `h_{i,k}` at `(i - 1, k - 1)`: the
coefficients of the sweeps, and `h_{k+1,k}` below the diagonal. `h_{ξ+1,ξ}`, the norm of the
last residual, is outside it, as in [1]'s (1) and the error bound (3) it enters.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `H = (h_{i,k})`, the entries `arnoldi` stores, restricted to the first `ξ` rows. -/
noncomputable def Krylov.arnoldiHessenberg (C : Mat ℝ n n) (v : Vec ℝ n) (ξ : ℕ) : Mat ℝ ξ ξ :=
  Matrix.of fun i k => (Krylov.arnoldi C v ξ).2 i k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
