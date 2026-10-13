import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.partPattern`

The exponent pattern of a dependent generator in the factors `V` (`E(ind_v, :)` for the column),
the rows outside `V` zeroed. `partZonotope` groups generators by it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pattern of generator `i` in the factors `V`. -/
def PolyZonotope.partPattern (pZ : PolyZonotope α) (V : Finset (Fin pZ.p)) (i : Fin pZ.h) :
    Fin pZ.p → ℕ :=
  fun k => if k ∈ V then pZ.E k i else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
