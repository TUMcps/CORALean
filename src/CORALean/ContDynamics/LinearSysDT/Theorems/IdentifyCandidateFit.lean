import CORALean.ContDynamics.LinearSysDT.Operations.IdentifyCandidate
import CORALean.Global.DmdBlocksStack
import CORALean.Global.DmdBlocksMulVec
import CORALean.Global.DmdCandidateFit

/-!
# The full-rank DMD candidate fits consistent data

If the data points obey `x(k+1) = A' x + B' u + c'` for some `(A', B', c')` and `X1 = V S Wᵀ` is an
SVD of the regressors with `s ≠ 0`, the blocks of the full-rank candidate satisfy it at every
point: `A x_j + B u_j + c = xNext_j`. Nothing about lower ranks, nor about data no such system
produced.
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

variable {n m N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.identifyCandidate_fit (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ m)
    (V : Mat ℝ (n + 1 + m) r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX1 : (Matrix.of fun i j => dmdRegressor (x j) (u j) i : Mat ℝ (n + 1 + m) N)
      = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0)
    (A' : Mat ℝ n n) (B' : Mat ℝ n m) (c' : Vec ℝ n)
    (hdata : ∀ j, xNext j = A' *ᵥ x j + B' *ᵥ u j + c') (j : Fin N) :
    (dmdBlocks (LinearSysDT.identifyCandidate xNext V s W r)).1 *ᵥ x j
      + (dmdBlocks (LinearSysDT.identifyCandidate xNext V s W r)).2.1 *ᵥ u j
      + (dmdBlocks (LinearSysDT.identifyCandidate xNext V s W r)).2.2 =
      xNext j := by -- --- PROOF ---
  -- the data is `X2 = G X1` for `G = [A' c' B']`
  have hG : (Matrix.of fun i j => xNext j i : Mat ℝ n N)
      = dmdStack A' B' c' * (Matrix.of fun i j => dmdRegressor (x j) (u j) i) := by
    ext i j
    have h := dmdBlocks_mulVec (dmdStack A' B' c') (x j) (u j)
    rw [dmdBlocks_dmdStack] at h
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [hdata j]
    exact (congrFun h i).symm
  -- the candidate fits the columns, and the blocks act as the matrix does
  have hfit := dmdCandidate_mul_eq _ _ V s W hX1 hV hW hs _ hG
  rw [← dmdBlocks_mulVec]
  have hcol : LinearSysDT.identifyCandidate xNext V s W r *ᵥ dmdRegressor (x j) (u j)
      = xNext j := by
    funext i
    have := congrFun (congrFun hfit i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, LinearSysDT.identifyCandidate] using this
  exact hcol

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
