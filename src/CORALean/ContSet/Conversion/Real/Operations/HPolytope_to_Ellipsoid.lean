module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A halfspace description as an ellipsoid — the construction

`HPolytope.ellipsoid` is the construction; `HPolytope_to_Ellipsoid` states and proves what it
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

noncomputable def HPolytope.ellipsoid (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Ellipsoid n :=
  (HPolytope.zonotope up lo).ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
