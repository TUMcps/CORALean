import CORALean.ContSet.HPolytope.Real.Theorems.InteriorNonemptyIffChebyshev
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# CORA's degeneracy program on a zero row

CORA's `@polytope/isFullDim.m` (`aux_isFullDim_nD_Hpoly_nosubspace`) normalizes the rows, then
solves `max r` subject to `A x + r ≤ b` with the *unnormalized* `A` and `b` and the coefficient
of `r` fixed at `1` — its comment says the norms are `1` "since we normalized the constraints",
but the normalized copy is not the one used. A zero row `0 x ≤ 0` then caps `r` at `0`: the
unit square with that row added is non-degenerate, yet every feasible `r` is at most `0`, so CORA
reports it degenerate. [1, Eq. 19] multiplies `r` by the row's norm, which is `0` there
(`HPolytope.ineqs_interior_nonempty_iff`).

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
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

theorem HPolytope.isFullDim_cora_counterexample :
    ∃ (A : Mat ℝ 5 2) (b : Vec ℝ 5), (interior (HPolytope.ineqs A b).construct).Nonempty ∧
      ∀ (x : Vec ℝ 2) (r : ℝ), (∀ j, (A *ᵥ x) j + r ≤ b j) → r ≤ 0 := by -- --- PROOF ---
  let A : Mat ℝ 5 2 := !![0, 0; 1, 0; -1, 0; 0, 1; 0, -1]
  have hA : ∀ x : Vec ℝ 2, A *ᵥ x = ![0, x 0, -x 0, x 1, -x 1] := fun x => by
    funext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨A, ![0, 1, 1, 1, 1], ?_, fun x r h => ?_⟩
  -- the ball of radius `1/2` around `0` fits: the zero row contributes `0 · r`
  · refine (HPolytope.ineqs_interior_nonempty_iff _ _).mpr ⟨0, 1 / 2, by norm_num, fun j => ?_⟩
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    fin_cases j <;> simp [A, norm₂, Fin.sum_univ_two] <;> norm_num
  -- the zero row: `0 + r ≤ 0`
  · have := h 0
    rw [hA] at this
    simpa using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
