import CORALean.Global.Tensor
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic

/-!
# The Gram matrix (5) inverts is singular for more data points than templates

[1, Eq. 5]: `(Φᵀ Φ)⁻¹` for `Φ` with `v` rows (templates) and `N = 2w + 1` columns (data
points). `Φᵀ Φ` is `N × N` of rank at most `v`, so its determinant is `0` once `N > v`: the
printed formula has no inverse to take. The paper's grid starts at `w = ⌈(v - 1)/2⌉`, where
`N ≥ v`, and goes to ten times that.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {v N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5]: `det(Φᵀ Φ) = 0` for `Φ` with fewer rows than columns. -/
theorem det_transpose_mul_self_eq_zero (Φ : Mat ℝ v N) (hvN : v < N) :
    (Φᵀ * Φ).det = 0 := by -- --- PROOF ---
  -- a unit would have rank `N`, but `Φᵀ Φ` has rank at most `v`
  by_contra h
  have hrank := Matrix.rank_of_isUnit (Φᵀ * Φ)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  have hle : (Φᵀ * Φ).rank ≤ v :=
    (Matrix.rank_mul_le_right Φᵀ Φ).trans ((Matrix.rank_le_card_height Φ).trans (by simp))
  rw [hrank, Fintype.card_fin] at hle
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
