module

public import CORALean.ContSet.Interval.Real.Operations.Kron
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Interval.kron` holds every Kronecker product of members

For `A` in the first box and `B` in the second, the Kronecker product `A ⊗ₖ B` (reindexed to
`Fin (m * p) × Fin (n * q)`) lies in the result. Only an outer statement: the entry `a_ij * b_kl`
reuses `a_ij` across every `(k, l)` and `b_kl` across every `(i, j)`, so the result's box holds
matrices that are no Kronecker product of members.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Kronecker

variable {m n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.kron_outer {I : Interval (Mat ℝ m n)} {J : Interval (Mat ℝ p q)}
    {A : Mat ℝ m n} {B : Mat ℝ p q} (hA : A ∈ I.construct) (hB : B ∈ J.construct) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) ∈
      (I.kron J).construct := by
  rintro ⟨r, c⟩
  simp only [Interval.kron, Entrywise.entry_mat, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Matrix.kroneckerMap_apply]
  exact Interval.mul_between_corners (hA (_, _)).1 (hA (_, _)).2 (hB (_, _)).1 (hB (_, _)).2


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
