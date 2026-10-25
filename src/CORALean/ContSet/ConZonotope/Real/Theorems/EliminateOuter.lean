module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveEqEliminate
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstraintReduceOuter

@[expose] public section

/-!
# `ConZonotope.eliminate` encloses

[1, Sec. 4.2] with Prop. 5: the partial-solve `Z̃` encloses `Z` for any `Λ_G`, `Λ_A`, so `eliminate`
does whenever `a_{rj} ≠ 0`. No bound on the other coefficients is needed for the enclosure;
exactness (`eliminate_exact_of_dependClosed`) is Raghuraman and Koeln's Thm. 2.

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

## Hypotheses
* `hAj` – pivot entry nonzero

## Conclusion
* the original set is contained in the eliminated set

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: `Z ⊂ Z̃` for the eliminated system, whenever `a_{rj} ≠ 0`. -/
theorem ConZonotope.eliminate_outer {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) :
    (ConZonotope.ofMat c G A b).construct
      ⊆ (ConZonotope.eliminate c G A b r j).construct :=
  (ConZonotope.partialSolve_eq_eliminate c G A b r j hAj) ▸
    ConZonotope.constraintReduce_outer c G A b _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
