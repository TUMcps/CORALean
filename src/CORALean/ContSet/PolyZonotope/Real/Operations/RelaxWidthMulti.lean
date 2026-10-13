module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ξ_E` summed over every factor

Split out of `RelaxExpMulti.lean` (issue #62): read again by the float layer's
own `relaxExpMulti` and by `Theorems/RelaxExpMultiOuter.lean` at both layers,
all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E` summed over every factor, the agreeing ones contributing nothing. -/
def PolyZonotope.relaxWidthMulti (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : ℕ :=
  ∑ k, PolyZonotope.eDiff (pZ.E k (part.right 0)) (pZ.E k (part.right 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
