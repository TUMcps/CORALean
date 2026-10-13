module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamGMulVec
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMul

@[expose] public section

/-!
# Partial solve zeroes column `j`

[1, Sec. 4.2]: with `Λ_G` and `Λ_A` of eq. 29, `G̃` and `Ã` have identically zero `j`-th
columns, "due to the elimination of `ξ_j`".

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: after eq. 29, column `j` of `G̃` and of `Ã` is zero. -/
theorem ConZonotope.partialSolve_zero_col {n q h : ℕ} (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) :
    (G j - ConZonotope.partialSolveΛG G A r j *ᵥ fun k => A k j) = 0 ∧
      ∀ i, (A - ConZonotope.partialSolveΛA A r j * A) i j = 0 := by -- --- PROOF ---
  refine ⟨?_, fun i => ?_⟩
  · rw [ConZonotope.partialSolveΛG_mulVec, smul_smul, mul_inv_cancel₀ hAj, one_smul, sub_self]
  · rw [Matrix.sub_apply, ConZonotope.partialSolveΛA_mul]
    field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
