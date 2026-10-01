import CORALean.ContSet.ConZonotope.Real.Operations.ConstraintReduce

/-!
# `ConZonotope.partialSolveΛA`

[1, Sec. 4.2]'s partial-solve dualization, before the zero row and column are removed: row `r` of
`Aξ = b` is solved for `ξ_j` (eq. 28) and substituted everywhere, which is `constraintReduce`
at the rank-one matrices of eq. 29, `Λ_G = G E_{jr} a_{rj}⁻¹` and `Λ_A = A E_{jr} a_{rj}⁻¹`.
The paper takes `r = 1`; `E_{jr}` is zero but for a one at `(j, r)`. Dropping the zero column
and row is `ConZonotope.eliminate`. The choice of `j` by the Hausdorff-error estimate `H_j`
(eqs. A.4-A.6) is a heuristic and is not formalized.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.2]: `Λ_A = A E_{jr} a_{rj}⁻¹`, whose only nonzero column is `r`, `a_j / a_{rj}`. -/
noncomputable def ConZonotope.partialSolveΛA {q h : ℕ} (A : Mat ℝ q h) (r : Fin q)
    (j : Fin h) : Mat ℝ q q :=
  Matrix.of fun i k => if k = r then A i j * (A r j)⁻¹ else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
