import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A nonnegative system keeps a nonnegative state

[1, Lemma 3]: every solution of `x_{k+1} = A x_k + w_k` with `A` and every `w_k` elementwise
nonnegative is elementwise nonnegative for all `k` once `x_0` is. By induction, a nonnegative
matrix mapping nonnegative vectors to nonnegative vectors.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem nonneg_of_nonneg_recurrence (A : Mat ℝ n n) (x w : ℕ → Vec ℝ n)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ k i, 0 ≤ w k i) (h0 : ∀ i, 0 ≤ x 0 i)
    (hstep : ∀ k, x (k + 1) = A *ᵥ x k + w k) (k : ℕ) (i : Fin n) :
    0 ≤ x k i := by -- --- PROOF ---
  induction k generalizing i with
  | zero => exact h0 i
  | succ k ih =>
    -- `A x_k ≥ 0` term by term, and `w_k ≥ 0`
    rw [hstep, Pi.add_apply, mulVec, dotProduct]
    refine add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (ih j)) (hw k i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
