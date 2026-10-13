module

public import CORALean.ContDynamics.LinearSys.Operations.IdentifyCandidate
public import CORALean.Global.DmdBlocksStack
public import CORALean.Global.DmdBlocksMulVec
public import CORALean.Global.DmdCandidateFit

@[expose] public section

/-!
# The full-rank DMD candidate fits consistent data

If the data points obey `ẋ = A' x + B' u + c'` for some `(A', B', c')` and `X1 = V S Wᵀ` is an
SVD of the regressors with `s ≠ 0`, the blocks of the full-rank candidate satisfy it at every
point: `A x_j + B u_j + c = dx_j`. Nothing about lower ranks, nor about data no such system
produced.
The source is [1].

## References

* [1] `contDynamics/@linearSys/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.identifyCandidate_fit (x dx : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ m)
    (V : Mat ℝ (n + 1 + m) r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX1 : (Matrix.of fun i j => dmdRegressor (x j) (u j) i : Mat ℝ (n + 1 + m) N)
      = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0)
    (A' : Mat ℝ n n) (B' : Mat ℝ n m) (c' : Vec ℝ n)
    (hdata : ∀ j, dx j = A' *ᵥ x j + B' *ᵥ u j + c') (j : Fin N) :
    (dmdBlocks (LinearSys.identifyCandidate dx V s W r)).1 *ᵥ x j
      + (dmdBlocks (LinearSys.identifyCandidate dx V s W r)).2.1 *ᵥ u j
      + (dmdBlocks (LinearSys.identifyCandidate dx V s W r)).2.2 =
      dx j := by -- --- PROOF ---
  -- the data is `X2 = G X1` for `G = [A' c' B']`
  have hG : (Matrix.of fun i j => dx j i : Mat ℝ n N)
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
  have hcol : LinearSys.identifyCandidate dx V s W r *ᵥ dmdRegressor (x j) (u j)
      = dx j := by
    funext i
    have := congrFun (congrFun hfit i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, LinearSys.identifyCandidate] using this
  exact hcol

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
