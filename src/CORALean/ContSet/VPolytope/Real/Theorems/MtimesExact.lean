module

public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact

@[expose] public section

/-!
# A matrix times a vertex description is exact

`map_exact` at `A *ᵥ ·`, once `mtimes` is known to be that map. The float layer
refines this one, paying its rounding into an error box around the mapped
vertices.

This is [1, Eq. 23]: the image of a V-polytope is the V-polytope of the images of its points.

## Inputs
* `n` – columns of the matrix
* `m` – rows of the matrix
* `M` – matrix
* `P` – polytope

## Hypotheses
* none

## Conclusion
* the image of `P` under `M` is exactly the result

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    (M *ᵥ ·) '' P.construct = (VPolytope.mtimes M P).construct := by
  rw [VPolytope.mtimes_eq_map]
  exact VPolytope.map_exact (Matrix.mulVecLin M) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
