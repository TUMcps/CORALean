module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.IdentifyCandidate
public import CORALean.Global.DmdCandidateFit

@[expose] public section

/-!
# The full-rank DMD candidate fits consistent data

If the data points obey xNext `= A' φ(x, u)` for some `A'` and `X1 = V S Wᵀ` is an SVD of the
basis values with `s ≠ 0`, the full-rank candidate satisfies it at every point: `A φ(x_j, u_j) =
xNext_j`. Nothing about lower ranks, nor about data no such system produced.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N r d : ℕ}


open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.identifyCandidate_fit (φ : Vec ℝ n → Vec ℝ m → Vec ℝ d) (x : Fin N → Vec ℝ n)
    (u : Fin N → Vec ℝ m) (xNext : Fin N → Vec ℝ n) (V : Mat ℝ d r) (s : Fin r → ℝ)
    (W : Mat ℝ N r)
    (hX1 : (Matrix.of fun i j => φ (x j) (u j) i : Mat ℝ d N) = V * Matrix.diagonal s * Wᵀ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (A' : Mat ℝ n d)
    (hdata : ∀ j, xNext j = A' *ᵥ φ (x j) (u j)) (j : Fin N) : -- --- STMT ---
    NonlinearSysDT.identifyCandidate xNext V s W r *ᵥ φ (x j) (u j) = xNext j := by -- --- PROOF ---
  -- the data is `X2 = A' X1`
  have hG : (Matrix.of fun i j => xNext j i : Mat ℝ n N)
      = A' * (Matrix.of fun i j => φ (x j) (u j) i : Mat ℝ d N) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [hdata j]
    rfl
  -- the candidate fits the columns
  have hfit := dmdCandidate_mul_eq _ _ V s W hX1 hV hW hs _ hG
  funext i
  have := congrFun (congrFun hfit i) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, NonlinearSysDT.identifyCandidate] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
