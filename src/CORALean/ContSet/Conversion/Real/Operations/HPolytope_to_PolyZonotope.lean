module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A halfspace description as a polynomial zonotope — the construction

`HPolytope.polyZonotope` is the construction; `HPolytope_to_PolyZonotope` states and proves what it
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

noncomputable def HPolytope.polyZonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : PolyZonotope (Vec ℝ n) :=
  (HPolytope.zonotope up lo).polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
