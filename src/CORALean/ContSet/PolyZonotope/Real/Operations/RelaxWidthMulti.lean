import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.Global.Partition

/-!
# `ξ_E` summed over every factor

Split out of `RelaxExpMulti.lean` (issue #62): read again by the float layer's
own `relaxExpMulti` and by `Theorems/RelaxExpMultiOuter.lean` at both layers,
all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E` summed over every factor, the agreeing ones contributing nothing. -/
def PolyZonotope.relaxWidthMulti (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) : ℕ :=
  ∑ k, PolyZonotope.eDiff (PZ.E k (part.right 0)) (PZ.E k (part.right 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
