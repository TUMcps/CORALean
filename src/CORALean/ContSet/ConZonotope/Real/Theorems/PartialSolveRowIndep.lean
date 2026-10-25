module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveConstructEq

@[expose] public section

/-!
# The partial-solve `Z̃` does not depend on the row it solves

[1, Sec. 4.2 (choice of j)]: eliminating `ξ_j` "using any constraint with `a_ij ≠ 0` gives the same
result (see A.4)". By `partialSolve_construct_eq` both sets are
`{Gξ + c : Aξ = b, |ξ_i| ≤ 1, ∀ i ≠ j}`, which names no row.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – first constraint row
* `r'` – second constraint row
* `j` – coefficient to eliminate

## Hypotheses
* `hAj` – first pivot entry nonzero
* `hAj'` – second pivot entry nonzero

## Conclusion
* the partial solve does not depend on the row used

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2 (choice of j)]: two rows `r`, `r'` with `a_rj ≠ 0 ≠ a_r'j` give the same `Z̃`. -/
theorem ConZonotope.partialSolve_row_indep {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r r' : Fin q) (j : Fin h) (hAj : A r j ≠ 0)
    (hAj' : A r' j ≠ 0) : -- --- CONCL ---
    (ConZonotope.partialSolve c G A b r j).construct
      = (ConZonotope.partialSolve c G A b r' j).construct := by -- --- PROOF ---
  rw [ConZonotope.partialSolve_construct_eq c G A b r j hAj,
    ConZonotope.partialSolve_construct_eq c G A b r' j hAj']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
