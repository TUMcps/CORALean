module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope

@[expose] public section

/-!
# A capsule as a polynomial zonotope — the construction

`Capsule.polyZonotope` is the construction; `Capsule_to_PolyZonotope` states and proves what it
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

noncomputable def Capsule.polyZonotope (C : Capsule n) : PolyZonotope (Vec ℝ n) :=
  C.interval.polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
