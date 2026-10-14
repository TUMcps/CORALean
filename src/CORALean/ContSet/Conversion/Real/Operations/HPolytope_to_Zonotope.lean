module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# A halfspace description as a zonotope — the construction

`HPolytope.zonotope` is the construction; `HPolytope_to_Zonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.zonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Zonotope (Vec ℝ n) :=
  (HPolytope.interval up lo).zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
