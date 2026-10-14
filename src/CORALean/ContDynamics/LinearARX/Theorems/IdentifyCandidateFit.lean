module

public import CORALean.ContDynamics.LinearARX.Operations.IdentifyCandidate
public import CORALean.ContDynamics.LinearARX.Theorems.IdentifyBlocksMulVec
public import CORALean.Global.DmdCandidateFit

@[expose] public section

/-!
# The full-rank DMD candidate fits consistent ARX data

If the data points obey the recursion of some ARX system `sys'` (outputs `y j`, inputs `u j`
at step `k j`, one signal pair per point; points of one trajectory repeat it) and
`X1 = V S Wᵀ` is an SVD of the regressors with `s ≠ 0`, the blocks of the full-rank candidate
satisfy it at every point. Nothing about lower ranks, nor about data no such system produced.
The source is [1].

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {dy du p N r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The matrix `[A B]` of a system, the inverse of `identifyBlocks`. -/
def aux_arxStack (sys : LinearARX ℝ dy du p) : Mat ℝ dy (p * dy + (p + 1) * du) :=
  fun a c => Fin.addCases
    (fun r => sys.Abar (finProdFinEquiv.symm r).1 a (finProdFinEquiv.symm r).2)
    (fun r => sys.Bbar (finProdFinEquiv.symm r).1 a (finProdFinEquiv.symm r).2) c

/-- The blocks of the stacked matrix are the system. -/
theorem aux_identifyBlocks_stack (sys : LinearARX ℝ dy du p) :
    LinearARX.identifyBlocks sys.dt (aux_arxStack sys) = sys := by
  cases sys
  simp only [LinearARX.identifyBlocks, aux_arxStack, Fin.addCases_left, Fin.addCases_right,
    Equiv.symm_apply_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.identifyCandidate_fit (y : Fin N → ℕ → Vec ℝ dy) (u : Fin N → ℕ → Vec ℝ du)
    (k : Fin N → ℕ) (V : Mat ℝ (p * dy + (p + 1) * du) r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX1 : (Matrix.of fun i j => LinearARX.identifyRegressor p (y j) (u j) (k j) i :
        Mat ℝ (p * dy + (p + 1) * du) N) = V * Matrix.diagonal s * Wᵀ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (sys' : LinearARX ℝ dy du p)
    (hdata : ∀ j, y j (k j) = ∑ i : Fin p, sys'.Abar i *ᵥ y j (k j - (i + 1))
      + ∑ l : Fin (p + 1), sys'.Bbar l *ᵥ u j (k j - l)) (j : Fin N) :
    y j (k j) = ∑ i : Fin p, (LinearARX.identifyBlocks sys'.dt (LinearARX.identifyCandidate
          (fun j => y j (k j)) V s W r)).Abar i *ᵥ y j (k j - (i + 1))
      + ∑ l : Fin (p + 1), (LinearARX.identifyBlocks sys'.dt (LinearARX.identifyCandidate
          (fun j => y j (k j)) V s W r)).Bbar l *ᵥ u j (k j - l) := by -- --- PROOF ---
  -- the data is `X2 = G X1` for `G = [A' B']`
  have hG : (Matrix.of fun i j => y j (k j) i : Mat ℝ dy N)
      = aux_arxStack sys' * (Matrix.of fun i j =>
        LinearARX.identifyRegressor p (y j) (u j) (k j) i) := by
    ext i j
    have h := LinearARX.identifyBlocks_mulVec sys'.dt (aux_arxStack sys') (y j) (u j) (k j)
    rw [aux_identifyBlocks_stack] at h
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [hdata j]
    exact (congrFun h i).symm
  -- the candidate fits the columns, and the blocks act as the matrix does
  have hfit := dmdCandidate_mul_eq _ _ V s W hX1 hV hW hs _ hG
  rw [← LinearARX.identifyBlocks_mulVec]
  funext i
  have := congrFun (congrFun hfit i) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, LinearARX.identifyCandidate] using this.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
