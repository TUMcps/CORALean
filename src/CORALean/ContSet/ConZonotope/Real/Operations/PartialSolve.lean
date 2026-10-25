module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamG
public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamA

@[expose] public section

/-!
# `ConZonotope.partialSolve`

[1, Sec. 4.2]'s partial-solve dualization, before the zero row and column are removed: row `r` of
`Aξ = b` is solved for `ξ_j` (eq. 28) and substituted everywhere, which is `constraintReduce`
at the rank-one matrices of eq. 29, `Λ_G = G E_{jr} a_{rj}⁻¹` and `Λ_A = A E_{jr} a_{rj}⁻¹`.
The paper takes `r = 1`; `E_{jr}` is zero but for a one at `(j, r)`. Dropping the zero column
and row is `ConZonotope.eliminate`. The choice of `j` by the Hausdorff-error estimate `H_j`
(eqs. A.4-A.6) is a heuristic and is not formalized.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – constraint row to solve
* `j` – coefficient to eliminate

## Output
* the set with row r solved for coefficient j

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.2]: `constraintReduce` at eq. 29's `Λ_G` and `Λ_A`, at full size. -/
noncomputable def ConZonotope.partialSolve {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) : ConZonotope (Vec ℝ n) :=
  ConZonotope.constraintReduce c G A b (ConZonotope.partialSolveΛG G A r j)
    (ConZonotope.partialSolveΛA A r j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
