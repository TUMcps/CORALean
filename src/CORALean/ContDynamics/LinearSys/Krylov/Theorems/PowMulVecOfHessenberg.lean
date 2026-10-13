import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Powers through a Hessenberg relation

The linear algebra behind the exactness of [1, Alg. 1]: if `C V e_k = V H e_k` for every column
`k` but the last (`k + 1 < m`) and `H` is upper Hessenberg (`H i k = 0` for `i > k + 1`), then
`C^j V x = V H^j x` for every `x` supported below index `m - j`. Each `H` moves the support of
`x` up by at most one, so `j` steps never reach the last column, the one whose relation carries
the residual `h_{m+1,m} v⁽ᵐ⁺¹⁾`. At `x = e₁` this is `C^j V e₁ = V H^j e₁` for `j < m`.

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

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `C^j V x = V H^j x` for `x` supported on the indices `i` with `i + j < m`. -/
theorem Krylov.pow_mulVec_of_hessenberg (C : Mat ℝ n n) (V : Mat ℝ n m) (H : Mat ℝ m m)
    (hH : ∀ i k : Fin m, (k : ℕ) + 1 < i → H i k = 0)
    (hrel : ∀ k : Fin m, (k : ℕ) + 1 < m → ∀ i, (C * V) i k = (V * H) i k)
    (j : ℕ) (x : Fin m → ℝ) (hx : ∀ i : Fin m, m ≤ (i : ℕ) + j → x i = 0) :
    C ^ j *ᵥ (V *ᵥ x) = V *ᵥ (H ^ j *ᵥ x) := by -- --- PROOF ---
  induction j generalizing x with
  | zero => simp only [pow_zero, one_mulVec]
  | succ j ih =>
    -- one step of `C` is one step of `H`, the relation being used only where `x` lives
    have hstep : C *ᵥ (V *ᵥ x) = V *ᵥ (H *ᵥ x) := by
      rw [mulVec_mulVec, mulVec_mulVec]
      funext i
      simp only [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : x k = 0
      · rw [hk, mul_zero, mul_zero]
      · have hlt : (k : ℕ) + 1 < m := by
          by_contra hc
          exact hk (hx k (by omega))
        rw [hrel k hlt i]
    -- `H x` is supported one index higher, so `j` more steps stay below the last column
    have hHx : ∀ i : Fin m, m ≤ (i : ℕ) + j → (H *ᵥ x) i = 0 := by
      intro i hi
      simp only [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : x k = 0
      · rw [hk, mul_zero]
      · have hlt : (k : ℕ) + 1 < i := by
          by_contra hc
          exact hk (hx k (by omega))
        rw [hH i k hlt, zero_mul]
    rw [pow_succ, ← mulVec_mulVec, hstep, ih (H *ᵥ x) hHx, pow_succ]
    exact congrArg (V *ᵥ ·) (mulVec_mulVec _ _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
