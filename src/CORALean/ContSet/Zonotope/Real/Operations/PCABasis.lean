import CORALean.ContSet.Zonotope.Real.Theorems.PCACovarianceIsHermitian
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `Zonotope.pcaBasis`

The principal axes of the dropped generators: an orthonormal eigenvector basis
of `pcaCovariance`, as the matrix whose columns they are. Mathlib's
`Matrix.IsHermitian.eigenvectorUnitary` is exactly that, and it comes as a
member of the unitary group rather than a bare matrix, which is what makes
`pcaBasis_isUnit_det` a one-liner and `reducePCA` free of the determinant
branch `reduceMethC` needs.

Noncomputable, and deliberately so: Mathlib's eigenvector basis is built from
the spectral theorem for symmetric operators and carries no algorithm. Nothing
at the `Real` layer is meant to run — a running PCA is a float-layer question,
and would be a different definition with an error bound of its own.

CORA reads the same axes off `svd(C)` [1], as [2, Alg. 2] does. On a positive-semidefinite `C` the
left singular vectors are eigenvectors, sorted by eigenvalue; Mathlib's are
not sorted, and neither the order of the columns nor their signs changes the
set `reduceByBasis` denotes.

## References

* [1] `contSet/@zonotope/private/priv_reducePCA.m`, CORA (Sep. 2025).
* [2] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The principal axes of the generators a partition drops: the columns of
Mathlib's unitary eigenvector matrix for `pcaCovariance`. -/
noncomputable def Zonotope.pcaBasis (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Mat ℝ n n :=
  ((Z.pcaCovariance_isHermitian part).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
