module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope

@[expose] public section

/-!
# A capsule as a halfspace description — the construction

`Capsule.hPolytope` is the construction; `Capsule_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Capsule.hPolytope (C : Capsule n) : HPolytope (Vec ℝ n) :=
  C.interval.hPolytope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
