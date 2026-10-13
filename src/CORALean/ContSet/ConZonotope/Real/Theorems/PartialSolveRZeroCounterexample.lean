import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveConstructEq
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# With Algorithm 1's `R`, `r_j = 0` does not make the partial solve exact

[1, Sec. 4.2 (choice of j)] selects `j` by first checking `r_j = 0`, and says that then "(A.1) and
(A.4) imply that `Z = Z̃` when `j` is selected", with `R` from Algorithm 1. Algorithm 1's `R` does
not satisfy (A.1) (`tightenER_not_superset`), and the conclusion fails on the same system.

The system is `-2ξ₁ + ξ₂ = 0` with `G = I`, `c = 0`. `Z` is the segment from `(-½, -1)` to
`(½, 1)`. Algorithm 1 returns `R₂ = [-1, 1]`, so `r₂ = 0`. But `Z̃ = {ξ : ξ₂ = 2ξ₁, |ξ₁| ≤ 1}`
is the segment from `(-1, -2)` to `(1, 2)`, and `(1, 2) ∈ Z̃ \ Z`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

-- evaluating Algorithm 1's two steps on the example symbolically needs more than the default
set_option maxHeartbeats 100000 in
/-- [1, Sec. 4.2 (choice of j)] fails: Algorithm 1's `R_j ⊆ [-1, 1]` (`r_j = 0`), yet `Z̃ ≠ Z`. -/
theorem ConZonotope.partialSolve_rZero_counterexample :
    ∃ (c : Vec ℝ 2) (G : Fin 2 → Vec ℝ 2) (A : Mat ℝ 1 2) (b : Vec ℝ 1) (r : Fin 1) (j : Fin 2),
      A r j ≠ 0 ∧ ((-1 : ℝ) : EReal) ≤ (ConZonotope.tightenER A b 0).2.1 j ∧
        (ConZonotope.tightenER A b 0).2.2 j ≤ 1 ∧
        (ConZonotope.partialSolve c G A b r j).construct
          ≠ (ConZonotope.ofMat c G A b).construct := by -- --- PROOF ---
  -- Algorithm 1's one pass, evaluated: `R₂ = [-1, 1]`
  have hR : ((-1 : ℝ) : EReal)
        ≤ (ConZonotope.tightenER (![![(-2 : ℝ), 1]] : Mat ℝ 1 2) (0 : Vec ℝ 1) 0).2.1 1 ∧
      (ConZonotope.tightenER (![![(-2 : ℝ), 1]] : Mat ℝ 1 2) (0 : Vec ℝ 1) 0).2.2 1 ≤ 1 := by
    unfold ConZonotope.tightenER ConZonotope.tightenPassER
    simp only [Fin.foldl_succ, Fin.foldl_zero]
    have he0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by ext x; fin_cases x <;> simp
    have he1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by ext x; fin_cases x <;> simp
    simp [ConZonotope.tightenCoeffER, ConZonotope.tightenCoeff, ConZonotope.rowBound, he0, he1]
    norm_num
  refine ⟨0, fun k => Pi.single k 1, ![![(-2 : ℝ), 1]], 0, 0, 1, by simp, hR.1, hR.2, ?_⟩
  -- `(1, 2)` is in `Z̃` by (A.4), and not in `Z`, whose coefficients are the point itself
  intro heq
  have hsum : ∀ ξ : Vec ℝ 2, ∑ k, ξ k • (Pi.single k 1 : Vec ℝ 2) = ξ := fun ξ => by
    funext i; fin_cases i <;> simp [Fin.sum_univ_two]
  have hin : (![1, 2] : Vec ℝ 2) ∈ (ConZonotope.partialSolve 0 (fun k => Pi.single k 1)
      ![![(-2 : ℝ), 1]] 0 0 1).construct := by
    rw [ConZonotope.partialSolve_construct_eq _ _ _ _ _ _ (by simp)]
    refine ⟨![1, 2], fun i hi => ?_, fun i => ?_, ?_⟩
    · fin_cases i
      · simp
      · exact absurd rfl hi
    · fin_cases i; simp [mulVec, dotProduct, Fin.sum_univ_two]
    · rw [zero_add, hsum]
  rw [heq, ConZonotope.mem_ofMat_iff] at hin
  obtain ⟨β, hβ, -, hx⟩ := hin
  rw [zero_add, hsum] at hx
  have h1 := hβ 1
  rw [← hx] at h1
  norm_num at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
