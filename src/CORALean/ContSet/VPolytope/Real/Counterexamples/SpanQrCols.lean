module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `[1, Eq. 20]` without pivoting

The points `±e₁, ±e₃ ∈ ℝ³` have mean `0`, so `V̄` is their matrix, of rank `2`. `Q = I`, `R = V̄`
is a QR decomposition — `R` is upper triangular, its middle row being zero — and its first two
columns span `{x₃ = 0}`, which misses `e₃`, a column of `V̄`. MATLAB's `qr` returns exactly this
`Q`, the Householder step being the identity on a column whose entries below the pivot vanish.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a QR factorization without pivoting whose columns miss the span

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.span_qr_cols_counterexample : -- --- CONCL ---
    ∃ (V : Mat ℝ 3 4) (Q : Mat ℝ 3 3) (R : Mat ℝ 3 4), Qᵀ * Q = 1 ∧ Q * R = V ∧
      (∀ (i : Fin 3) (j : Fin 4), (j : ℕ) < i → R i j = 0) ∧ V.rank = 2 ∧
      V.col 2 ∉ Submodule.span ℝ (Set.range fun j : Fin 2 => Q.col (Fin.castLE (by norm_num)
      j)) := by -- --- PROOF ---
  let V : Mat ℝ 3 4 := !![1, -1, 0, 0; 0, 0, 0, 0; 0, 0, 1, -1]
  refine ⟨V, 1, V, by simp, by simp, ?_, le_antisymm ?_ ?_, ?_⟩
  -- the middle row is zero and the last row starts with two zeros
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp at hji ⊢ <;> simp [V]
  -- rank at most two: `V` factors through `ℝ²`
  · have hfac : V =
        (!![1, 0; 0, 0; 0, 1] : Mat ℝ 3 2) * (!![1, -1, 0, 0; 0, 0, 1, -1] : Mat ℝ 2 4) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hfac]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)
  -- rank at least two: rows `1, 3` and columns `1, 3` of `V` make the identity
  · have hid : (!![1, 0, 0; 0, 0, 1] : Mat ℝ 2 3) * V * (!![1, 0; 0, 0; 0, 1; 0, 0] : Mat ℝ 4 2) =
        (1 : Mat ℝ 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [V, Matrix.mul_apply, Fin.sum_univ_succ]
    have h2 : (1 : Mat ℝ 2 2).rank = 2 := by
      rw [Matrix.rank_one, Fintype.card_fin]
    rw [← h2, ← hid]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  -- the span of `e₁, e₂` has third coordinate zero
  · intro hmem
    have hle : Submodule.span ℝ (Set.range fun j : Fin 2 => (1 : Mat ℝ 3 3).col
        (Fin.castLE (by norm_num) j)) ≤ LinearMap.ker (LinearMap.proj 2 : Vec ℝ 3 →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      fin_cases j <;> simp [Matrix.col]
    have := hle hmem
    simp [V, Matrix.col] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
