module

public import CORALean.ContSet.Zonotope.Real.Theorems.PCACovarianceIsHermitian
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# `Zonotope.pcaBasis`

The principal axes of the dropped generators: an orthonormal eigenvector basis of
`pcaCovariance`, as the matrix whose columns they are. Mathlib's
`Matrix.IsHermitian.eigenvectorUnitary` is exactly that, as a member of the unitary group, which
makes `pcaBasis_isUnit_det` a one-liner. Noncomputable, deliberately: the basis comes from the
spectral theorem and carries no algorithm; a running PCA is a float-layer question. CORA reads the
same axes off `svd(C)` [1], as [2, Alg. 2] does. On a positive-semidefinite `C` the left singular
vectors are eigenvectors, sorted by eigenvalue; Mathlib's are not, and neither the order nor the
signs of the columns changes the set `reduceByBasis` denotes.

## Inputs
* `Z` – zonotope
* `part` – split of the generators

## Output
* principal axes of the dropped generators

## References

* [1] `contSet/@zonotope/private/priv_reducePCA.m`, CORA (Sep. 2025).
* [2] [A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of Zonotopes". 2017
      IEEE 56th Annual Conference on Decision and Control (CDC),
      2017.](../../../../../../references/2017/kopetzki-cdc-order-reduction.md)
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
