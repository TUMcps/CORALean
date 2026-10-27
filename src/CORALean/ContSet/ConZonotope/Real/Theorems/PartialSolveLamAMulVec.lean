module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve

@[expose] public section

/-!
# `Λ_A b` of [1, Sec. 4.2]

`Λ_A` of [1, Sec. 4.2] is zero off column `r`, so `Λ_A b` is the same correction on the
right-hand side: `(Λ_A b)_i = a_{ij} b_r / a_{rj}`.

## Inputs
* `q` – number of constraints
* `h` – number of generators
* `A` – constraint matrix
* `r` – constraint row to solve
* `j` – coefficient to eliminate
* `b` – constraint offset
* `i` – row index

## Hypotheses
* none

## Conclusion
* the entry of the multiplier times the offset is a rank-one correction

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
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
