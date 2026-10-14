module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# A capsule as a zonotope — the construction

`Capsule.zonotope` is the construction; `Capsule_to_Zonotope` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Capsule.zonotope (C : Capsule n) : Zonotope (Vec ℝ n) :=
  C.interval.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
