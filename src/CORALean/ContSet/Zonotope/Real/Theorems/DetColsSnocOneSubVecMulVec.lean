module

public import CORALean.ContSet.Zonotope.Real.Definitions.ColsSnoc
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# Mapping all columns by I - λcᵀ leaves a determinant with the column σλ unchanged

`det [(I - λcᵀ) B σλ] = det [B σλ]`, the step of the derivation in [1, Sec. 6.1] that "the
determinant of a matrix does not change if a column is added or subtracted from another one": the
columns `(I - λcᵀ) B_k = B_k - (cᵀB_k) λ` differ from `B_k` by multiples of the last column.
Written as `[B σλ]` times `I + e_last wᵀ`, of determinant `1 + w_last = 1` (matrix determinant
lemma), for `σ ≠ 0`; both determinants vanish at `σ = 0`.

## Inputs
* `c` – row vector
* `l` – column vector
* `σ` – scalar
* `B` – list of columns

## Hypotheses
* none

## Conclusion
* the determinant is unchanged by the rank-one update

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem det_colsSnoc_one_sub_vecMulVec (c l : Vec ℝ (m + 1)) (σ : ℝ)
    (B : Fin m → Vec ℝ (m + 1)) : -- --- CONCL ---
    (colsSnoc (fun k => (1 - Matrix.vecMulVec l c) *ᵥ B k) (σ • l)).det =
      (colsSnoc B (σ • l)).det := by -- --- PROOF ---
  by_cases hσ : σ = 0
  · -- the last column is zero in both
    subst hσ
    rw [Matrix.det_eq_zero_of_column_eq_zero (Fin.last m),
      Matrix.det_eq_zero_of_column_eq_zero (Fin.last m)] <;> intro i <;> simp [colsSnoc]
  · -- the column operation, as a product with `I + e_last wᵀ`
    let w : Fin (m + 1) → ℝ := fun k => Fin.lastCases 0 (fun k' => -(c ⬝ᵥ B k') / σ) k
    have hE : (colsSnoc B (σ • l)) * (1 + Matrix.replicateCol Unit
        (Pi.single (Fin.last m) (1 : ℝ)) * Matrix.replicateRow Unit w) =
        colsSnoc (fun k => (1 - Matrix.vecMulVec l c) *ᵥ B k) (σ • l) := by
      ext i k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [colsSnoc, w, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
          Matrix.replicateCol, Matrix.replicateRow, Pi.single_apply]
      · simp [colsSnoc, w, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
          Matrix.replicateCol, Matrix.replicateRow, Pi.single_apply, Matrix.sub_mulVec,
          Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Fin.sum_univ_castSucc]
        field_simp
        have h : Fin.last m ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
        simp only [h, if_false, mul_zero, zero_add, mul_assoc,
          ← Finset.mul_sum]
        ring
    rw [← hE, Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [w, dotProduct, Pi.single_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
