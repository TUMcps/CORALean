module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope — the construction

`HPolytope.conPolyZono` is the construction; `HPolytope_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.conPolyZono (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ConPolyZono (Vec ℝ n) :=
  (HPolytope.polyZonotope up lo).conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
