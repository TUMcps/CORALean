module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ZonoBundle.dirPcaCovariance`: the scatter of a vertex cloud

What the pca method of [1, Heuristic pca] takes its principal axes of: the covariance of the
vertices of the bundle, `∑ₗ (vₗ - μ)(vₗ - μ)ᵀ` with `μ` their mean, without the positive factor a
sample covariance divides by. The paper says this needs vertex computation, which the bundle's
representation does not provide, so the vertices come in as an argument.

## Inputs
* `m` – number of vertices
* `V` – vertices

## Output
* the covariance matrix of the vertices

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The scatter matrix of the vertices `V`, about their mean, as in [1, Heuristic pca]. -/
noncomputable def ZonoBundle.dirPcaCovariance {m : ℕ} (V : Fin m → Vec ℝ n) : Mat ℝ n n :=
  Matrix.of fun i j =>
    ∑ l, (V l i - (∑ l', V l' i) / m) * (V l j - (∑ l', V l' j) / m)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
