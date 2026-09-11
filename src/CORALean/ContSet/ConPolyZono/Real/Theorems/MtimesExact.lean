import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact

/-!
# A matrix times a constrained polynomial zonotope is exact

The result is [1, Prop. 5].

`map_exact` at `A *ᵥ ·`, which is the case reachability runs. The constraint is
on the factors, and a linear map of the ambient space moves points, not factors.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mtimes_exact {k n : ℕ} (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (M *ᵥ ·) '' cPZ.construct = (ConPolyZono.mtimes M cPZ).construct :=
  ConPolyZono.map_exact (Matrix.mulVecLin M) cPZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
