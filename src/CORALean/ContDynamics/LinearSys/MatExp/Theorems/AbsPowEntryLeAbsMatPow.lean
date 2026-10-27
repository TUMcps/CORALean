module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat

@[expose] public section

/-!
# `|Aⁱ_{jk}| ≤ (|A|ⁱ)_{jk}`, entrywise

By induction on `i`: the base case is the identity matrix, equal on both sides; the step expands
`Aⁱ⁺¹ = Aⁱ·A` via `Matrix.mul_apply`, bounds the sum of products by the triangle inequality, and
bounds each product's first factor by the inductive hypothesis against `A`'s entrywise absolute
value; the second factor, `|A l k|`, already equals `(MatExp.absMat A) l k`. [1]'s `E(Δt,η)` is
built from `MatExp.absMat A`, and its entrywise domination of the particular solution's own tail
needs this to compare `Aⁱ`'s contribution against it order by order.

## Inputs
* `A` – matrix
* `i` – power
* `j` – row index
* `k` – column index

## Hypotheses
* none

## Conclusion
* the power's entry is at most the absolute-value power's entry

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A matrix power's entry never exceeds, in magnitude, the same entry of the power of its own
entrywise absolute value. -/
theorem abs_pow_entry_le_absMat_pow_entry (A : Mat ℝ n n) (i : ℕ) (j k : Fin n) : -- --- CONCL ---
    |(A ^ i) j k| ≤ (MatExp.absMat A ^ i) j k := by -- --- PROOF ---
  induction i generalizing j k with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> simp
  | succ i ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    -- the triangle inequality on the product, then the inductive bound factor by factor
    calc |∑ l, (A ^ i) j l * A l k|
        ≤ ∑ l, |(A ^ i) j l * A l k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |(A ^ i) j l| * (MatExp.absMat A) l k :=
          Finset.sum_congr rfl fun l _ => by rw [abs_mul]; rfl
      _ ≤ ∑ l, (MatExp.absMat A ^ i) j l * (MatExp.absMat A) l k :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (ih j l) (abs_nonneg _)
      _ = (MatExp.absMat A ^ (i + 1)) j k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
