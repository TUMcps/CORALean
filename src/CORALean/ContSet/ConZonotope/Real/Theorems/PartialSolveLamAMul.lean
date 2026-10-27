module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve

@[expose] public section

/-!
# `Λ_A A` of [1, Sec. 4.2]

`Λ_A` of [1, Sec. 4.2] is zero off column `r`, so `Λ_A A` is the rank-one correction
`(Λ_A A)_{il} = a_{ij} a_{rl} / a_{rj}`.

## Inputs
* `q` – number of constraints
* `h` – number of generators
* `A` – constraint matrix
* `r` – constraint row to solve
* `j` – coefficient to eliminate
* `i` – row index
* `l` – column index

## Hypotheses
* none

## Conclusion
* the entry of the multiplier times the matrix is a rank-one correction

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: `Λ_A A` is the rank-one correction `a_{ij} a_{rl} / a_{rj}`. -/
theorem ConZonotope.partialSolveΛA_mul {q h : ℕ} (A : Mat ℝ q h) (r : Fin q) (j : Fin h)
    (i : Fin q) (l : Fin h) :
    (ConZonotope.partialSolveΛA A r j * A) i l = A i j * (A r j)⁻¹ * A r l := by
  simp [ConZonotope.partialSolveΛA, Matrix.mul_apply, ite_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
