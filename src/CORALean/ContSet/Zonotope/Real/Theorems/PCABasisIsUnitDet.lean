module

public import CORALean.ContSet.Zonotope.Real.Operations.PCABasis

@[expose] public section

/-!
# The principal-axis basis is invertible

`reduceByBasis_outer` holds at every `P` whose determinant is a unit, and this
is that hypothesis for `pcaBasis` [1, Alg. 2], discharged once and for all rather than
tested at each call as `reduceMethC` must test its search's answer.

Nothing about eigenvectors is needed for it. `pcaBasis` is by definition the
matrix underlying a member of Mathlib's unitary group, and a unitary matrix's
determinant is a unit because `U * Uᵀ = 1` makes it one — over `ℝ` that is an
orthogonal matrix, whose determinant is `±1`. So the proof is Mathlib's
`Matrix.UnitaryGroup.det_isUnit` applied to the member `pcaBasis` unfolds to,
and it would read the same for any Hermitian matrix whatever.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The principal axes form an invertible basis, which is what `reduceByBasis`
asks of the matrix it boxes along. -/
theorem Zonotope.pcaBasis_isUnit_det (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    IsUnit (Z.pcaBasis part).det :=
  Matrix.UnitaryGroup.det_isUnit _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
