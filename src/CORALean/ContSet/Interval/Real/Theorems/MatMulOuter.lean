module

public import CORALean.ContSet.Interval.Real.Operations.MatMul
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Interval.matMul` over-approximates every product of two matrices in the boxes

Entry `(i, j)` of `M * N` is `∑ k, M i k * N k j` (`Matrix.mul_apply`), each
summand between the corresponding `mulLo`/`mulHi` by `mul_between_corners`, and
`Finset.sum_le_sum` twice finishes it — the same shape as `mtimesIntervalMat`'s.

Outer and never exact: the `k` summands are bounded independently although they come from one
pair of matrices, so a product entry that would need two different `k`-corners at once is
admitted. The usual interval-arithmetic dependency loss, and why Althoff §3.3.2 moves to matrix
zonotopes. [1, Eq. 16], an enclosure, as the paper defines it.

## Inputs
* `A` – left interval matrix
* `B` – right interval matrix
* `M` – member of the left matrix
* `N` – member of the right matrix

## Hypotheses
* `hM` – `M` lies in `A`
* `hN` – `N` lies in `B`

## Conclusion
* the product `M N` lies in the result

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matMul_outer (A : Interval (Mat ℝ m n)) (B : Interval (Mat ℝ n p))
    {M : Mat ℝ m n} (hM : M ∈ A.construct) {N : Mat ℝ n p} (hN : N ∈ B.construct) : -- --- CONCL ---
    M * N ∈ (Interval.matMul A B).construct := by -- --- PROOF ---
  have hM' := Interval.mem_mat_iff.mp hM
  have hN' := Interval.mem_mat_iff.mp hN
  intro q
  obtain ⟨i, j⟩ := q
  show (∑ k, Interval.mulLo (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j))
        ≤ (M * N) i j
      ∧ (M * N) i j
        ≤ ∑ k, Interval.mulHi (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)
  rw [Matrix.mul_apply]
  exact ⟨Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_corners (hM' i k).1 (hM' i k).2
             (hN' k j).1 (hN' k j).2).1,
         Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_corners (hM' i k).1 (hM' i k).2
             (hN' k j).1 (hN' k j).2).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
