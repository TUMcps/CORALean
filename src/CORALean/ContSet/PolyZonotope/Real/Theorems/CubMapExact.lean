module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CubMapDepExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact

@[expose] public section

/-!
# `PolyZonotope.cubMap` is exact

`{ (xᵀ T x) * x | x ∈ pZ } = pZ.cubMap T`, `zᵢ = Σₖ xₖ (xᵀ T{i,k} x)`: the cubic map of a polynomial
zonotope is a polynomial zonotope, with no enclosure. The pointwise form is `cubMapDepOn_point`:
the point of the result at every factor vector is the cubic map of the original's point there.

## Inputs
* `T` – family of cubic form tensors
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the cubic image of the set equals the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
