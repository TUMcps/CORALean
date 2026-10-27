module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `Λ_G` of [1, Sec. 4.2] on a vector

`Λ_G` of [1, Sec. 4.2] is zero off column `r`, so it reads only entry `r` of its argument:
`Λ_G v = v_r g_j / a_{rj}`.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `G` – generators
* `A` – constraint matrix
* `r` – constraint row to solve
* `j` – coefficient to eliminate
* `v` – vector

## Hypotheses
* none

## Conclusion
* the multiplier applied to the vector reads only entry r

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

/-- [1, Sec. 4.2]: `Λ_G` only reads row `r` of its argument. -/
theorem ConZonotope.partialSolveΛG_mulVec {n q h : ℕ} (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (r : Fin q) (j : Fin h) (v : Vec ℝ q) :
    ConZonotope.partialSolveΛG G A r j *ᵥ v = v r • ((A r j)⁻¹ • G j) := by
  funext i
  simp [ConZonotope.partialSolveΛG, Matrix.mulVec, dotProduct, ite_mul]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
