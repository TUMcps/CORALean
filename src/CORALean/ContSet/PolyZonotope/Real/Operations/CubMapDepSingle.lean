import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep

/-!
# `PolyZonotope.cubMapDep`

`cubMapDepOn` of a set in its own ambient space: the single form `{ (xᵀ T x) * x | x ∈ pZ }`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cubMapDepOn` with the identity three times. -/
def PolyZonotope.cubMapDep (T : Fin m → Fin n → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) :=
  PolyZonotope.cubMapDepOn LinearMap.id LinearMap.id LinearMap.id T pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
