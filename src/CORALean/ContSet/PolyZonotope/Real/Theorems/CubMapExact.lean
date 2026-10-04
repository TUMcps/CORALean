import CORALean.ContSet.PolyZonotope.Real.Operations.CubMap
import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
import CORALean.ContSet.PolyZonotope.Real.Theorems.CubMapDepExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact

/-!
# `PolyZonotope.cubMap` is exact

`{ (xᵀ T x) * x | x ∈ pZ } = pZ.cubMap T`, `zᵢ = Σₖ xₖ (xᵀ T{i,k} x)`: the cubic map of a polynomial
zonotope is a polynomial zonotope, with no enclosure. The pointwise form is `cubMapDepOn_point`:
the point of the result at every factor vector is the cubic map of the original's point there.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMap_exact (T : Fin m → Fin n → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    cubEval T '' pZ.construct = (pZ.cubMap T).construct := by
  rw [pZ.dependent_exact]
  exact PolyZonotope.cubMapDep_exact T pZ.dependent rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
