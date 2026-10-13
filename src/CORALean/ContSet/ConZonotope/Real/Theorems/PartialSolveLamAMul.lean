module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve

@[expose] public section

/-!
# `Λ_A A` of [1, Sec. 4.2]

`Λ_A` of [1, Sec. 4.2] is zero off column `r`, so `Λ_A A` is the rank-one correction
`(Λ_A A)_{il} = a_{ij} a_{rl} / a_{rj}`.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: `Λ_A A` is the rank-one correction `a_{ij} a_{rl} / a_{rj}`. -/
theorem ConZonotope.partialSolveΛA_mul {q h : ℕ} (A : Mat ℝ q h) (r : Fin q) (j : Fin h)
    (i : Fin q) (l : Fin h) :
    (ConZonotope.partialSolveΛA A r j * A) i l = A i j * (A r j)⁻¹ * A r l := by
  simp [ConZonotope.partialSolveΛA, Matrix.mul_apply, ite_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
