import CORALean.ContDynamics.Conform.Theorems.ProdJacSucc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# Unrolling an affine recursion with time-varying matrices

`d_{m+1} = A_m d_m + w_m` gives `d_M = (A_{M-1} ⋯ A_0) d_0 + ∑_{i<M} (A_{M-1} ⋯ A_{i+1}) w_i`,
with `prodJac A M j` the product of the latest `j` factors. This is the recursion inserted
into itself, which [1, Cor. 1] and [1, Cor. 2] state as the GLO matrices.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The solution of `d_{m+1} = A_m d_m + w_m`, as a product of the latest factors. -/
theorem Conform.unroll_affine (A : ℕ → Mat ℝ n n) (d w : ℕ → Vec ℝ n)
    (h : ∀ m, d (m + 1) = A m *ᵥ d m + w m) (M : ℕ) :
    d M = Conform.prodJac A M M *ᵥ d 0
      + ∑ i ∈ Finset.range M, Conform.prodJac A M (M - i - 1) *ᵥ w i := by -- --- PROOF ---
  induction M with
  | zero => simp [Conform.prodJac]
  | succ M ih =>
    rw [h M, Finset.sum_range_succ, show M + 1 - M - 1 = 0 by omega, Conform.prodJac_succ]
    -- the earlier terms each gain the factor `A_M` on the left
    have hsum : ∑ i ∈ Finset.range M, Conform.prodJac A (M + 1) (M + 1 - i - 1) *ᵥ w i
        = A M *ᵥ ∑ i ∈ Finset.range M, Conform.prodJac A M (M - i - 1) *ᵥ w i := by
      rw [mulVec_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show M + 1 - i - 1 = (M - i - 1) + 1 by omega, Conform.prodJac_succ, ← mulVec_mulVec]
    rw [hsum, ih, ← mulVec_mulVec]
    simp only [Conform.prodJac, List.range_zero, List.map_nil, List.prod_nil, one_mulVec,
      mulVec_add]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
