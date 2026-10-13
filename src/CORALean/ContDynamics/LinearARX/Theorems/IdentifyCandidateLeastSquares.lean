import CORALean.ContDynamics.LinearARX.Operations.IdentifyCandidate
import CORALean.ContDynamics.LinearARX.Operations.IdentifyRegressor
import CORALean.Global.DmdCandidateLeastSquares

/-!
# The full-rank DMD candidate is a least-squares fit of the ARX recursion

For any data, consistent with an ARX system or not, and the SVD `X1 = V S Wᵀ` of the
regressors with `s ≠ 0`: no matrix `[A B]` has a smaller sum of squared residuals
`y(j) - [A B] x_j` over the data points than the full-rank candidate [1, Eq. 2.7].

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {dy du p N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.identifyCandidate_leastSquares (y : Fin N → ℕ → Vec ℝ dy)
    (u : Fin N → ℕ → Vec ℝ du) (k : Fin N → ℕ) (V : Mat ℝ (p * dy + (p + 1) * du) r)
    (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX1 : (Matrix.of fun i j => LinearARX.identifyRegressor p (y j) (u j) (k j) i :
        Mat ℝ (p * dy + (p + 1) * du) N) = V * Matrix.diagonal s * Wᵀ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0)
    (B : Mat ℝ dy (p * dy + (p + 1) * du)) :
    ∑ j, ∑ a, (y j (k j) a - (LinearARX.identifyCandidate (fun j => y j (k j)) V s W r
        *ᵥ LinearARX.identifyRegressor p (y j) (u j) (k j)) a) ^ 2
      ≤ ∑ j, ∑ a, (y j (k j) a
        - (B *ᵥ LinearARX.identifyRegressor p (y j) (u j) (k j)) a) ^ 2 := by -- --- PROOF ---
  -- the matrix form of the global least-squares theorem, entry by entry
  have h := dmdCandidate_leastSquares (Matrix.of fun i j => y j (k j) i)
    (Matrix.of fun i j => LinearARX.identifyRegressor p (y j) (u j) (k j) i) V s W hX1 hV hW hs B
  simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    LinearARX.identifyCandidate] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
