import CORALean.ContSet.ZonoBundle.Real.Theorems.DirPcaCovarianceIsHermitian
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `ZonoBundle.dirPca`: the pca heuristic

The pca method of [1, Heuristic pca]: `Λ` the directions of greatest variance of the bundle's
vertices, an orthonormal eigenvector basis of their scatter matrix, as Mathlib's unitary
eigenvector matrix. Noncomputable as Mathlib's spectral theorem is: a running PCA is a float-layer
question. The vertices are an argument, since the paper's rule needs them computed first.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pca method [1, Heuristic pca]: the principal axes of the vertices `V` as columns. -/
noncomputable def ZonoBundle.dirPca {m : ℕ} (V : Fin m → Vec ℝ n) : Mat ℝ n n :=
  ((ZonoBundle.dirPcaCovariance_isHermitian V).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
