module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve

@[expose] public section

/-!
# `Λ_A b` of [1, Sec. 4.2]

`Λ_A` of [1, Sec. 4.2] is zero off column `r`, so `Λ_A b` is the same correction on the
right-hand side: `(Λ_A b)_i = a_{ij} b_r / a_{rj}`.

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

/-- [1, Sec. 4.2]: `Λ_A b` is the correction `a_{ij} b_r / a_{rj}`. -/
theorem ConZonotope.partialSolveΛA_mulVec {q h : ℕ} (A : Mat ℝ q h) (r : Fin q)
    (j : Fin h) (b : Vec ℝ q) (i : Fin q) :
    (ConZonotope.partialSolveΛA A r j *ᵥ b) i = A i j * (A r j)⁻¹ * b r := by
  simp [ConZonotope.partialSolveΛA, Matrix.mulVec, dotProduct, ite_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
