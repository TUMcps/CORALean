module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `R_j` of [1, Alg. 1 (R)] need not contain `{ξ_j | Aξ = b, |ξ_i| ≤ 1 ∀ i ≠ j}`

[1, Alg. 1 (R)] and [2, Alg. 1] say Algorithm 1 returns `R` with
`R_j ⊃ {ξ_j | Aξ = b, |ξ_i| ≤ 1, ∀ i ≠ j}`. It does not. The bound on `R_j` is computed from
the running `E`, and `E` was tightened by earlier steps that used `|ξ_j| ≤ 1`.

The one-row system is `-2ξ₁ + ξ₂ = 0`. The first step solves for `ξ₁` and gets
`E₁ = [-½, ½]`, using `|ξ₂| ≤ 1`. The second solves for `ξ₂ = 2ξ₁` from `E₁` and gets
`R₂ = [-1, 1]`. But `ξ = (1, 2)` satisfies the row with `|ξ₁| ≤ 1`, and `ξ₂ = 2 ∉ R₂`.
What `R` does contain is `B∞(A, b)`'s own projection (`tightenER_outer`), which is all the
emptiness test needs.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
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

/-- [1, Alg. 1 (R)], [2, Alg. 1] fail: a feasible `ξ` with `|ξ_i| ≤ 1` for `i ≠ j` whose
`ξ_j` lies above Algorithm 1's `R_j`. -/
theorem ConZonotope.tightenER_not_superset :
    ∃ (A : Mat ℝ 1 2) (b : Vec ℝ 1) (ξ : Vec ℝ 2) (j : Fin 2),
      (∀ i, (A *ᵥ ξ) i = b i) ∧ (∀ i, i ≠ j → |ξ i| ≤ 1) ∧
        (ConZonotope.tightenER A b 0).2.2 j < (ξ j : EReal) := by -- --- PROOF ---
  refine ⟨![![(-2 : ℝ), 1]], 0, ![1, 2], 1, ?_, ?_, ?_⟩
  · -- `-2·1 + 2 = 0`
    intro i
    fin_cases i
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  · -- the only other coordinate is `ξ₁ = 1`
    intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi
  · -- the two steps of the one pass, evaluated: `R₂ = [-1, 1]`
    have hR : (ConZonotope.tightenER (![![(-2 : ℝ), 1]] : Mat ℝ 1 2) (0 : Vec ℝ 1) 0).2.2 1
        ≤ 1 := by
      unfold ConZonotope.tightenER ConZonotope.tightenPassER
      simp only [Fin.foldl_succ, Fin.foldl_zero]
      have he0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by ext x; fin_cases x <;> simp
      have he1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by ext x; fin_cases x <;> simp
      simp [ConZonotope.tightenCoeffER, ConZonotope.tightenCoeff, ConZonotope.rowBound, he0, he1]
      norm_num
    refine lt_of_le_of_lt hR ?_
    show ((1 : ℝ) : EReal) < ((2 : ℝ) : EReal)
    exact EReal.coe_lt_coe_iff.mpr (by norm_num)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
