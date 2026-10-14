module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

@[expose] public section

/-!
# A capsule as a vertex description — the construction

`Capsule.vPolytope` is the construction; `Capsule_to_VPolytope` states and proves what it
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

noncomputable def Capsule.vPolytope (C : Capsule n) : VPolytope (Vec ℝ n) :=
  C.interval.vPolytope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
