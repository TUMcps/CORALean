module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Powers of a nonnegative matrix are monotone, entrywise

If `0 ≤ B ≤ C` entrywise then `0 ≤ Bᵏ ≤ Cᵏ` entrywise, by induction on `k` with `Bᵏ⁺¹ = Bᵏ * B`:
each summand is a product of two nonnegative entries, each no greater than the matching one of `C`.
It carries the domination `|M| ≤ |A|` of the members of an interval matrix to their powers.

## Inputs
* `B` – smaller matrix
* `C` – larger matrix
* `k` – exponent
* `i` – row index
* `j` – column index

## Hypotheses
* `hB` – smaller matrix entrywise nonnegative
* `h` – smaller matrix entrywise at most the larger

## Conclusion
* the power of the smaller matrix is nonnegative and at most the power of the larger
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `0 ≤ B ≤ C` entrywise gives `0 ≤ Bᵏ ≤ Cᵏ` entrywise. -/
theorem MatExp.pow_entry_le_pow_entry {B C : Mat ℝ n n} (hB : ∀ i j, 0 ≤ B i j)
    (h : ∀ i j, B i j ≤ C i j) (k : ℕ) (i j : Fin n) : -- --- CONCL ---
    0 ≤ (B ^ k) i j ∧ (B ^ k) i j ≤ (C ^ k) i j := by -- --- PROOF ---
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    exact ⟨Finset.sum_nonneg fun l _ => mul_nonneg (ih i l).1 (hB l j),
      Finset.sum_le_sum fun l _ =>
        mul_le_mul (ih i l).2 (h l j) (hB l j) ((ih i l).1.trans (ih i l).2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
