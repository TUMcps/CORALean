import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

/-!
# A matrix times a polynomial zonotope is exact

The result is [1, Prop. 8].

`map_exact` at `A *ᵥ ·`, which is the case reachability runs. The exponent
matrix never enters: the monomials are scalars, so a linear map of the ambient
space cannot touch them.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   21-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' pZ.construct = (PolyZonotope.mtimes M pZ).construct :=
  PolyZonotope.map_exact (Matrix.mulVecLin M) pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
