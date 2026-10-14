module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A capsule as a box — the construction

`Capsule.interval` is the construction; `Capsule_to_Interval` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.interval (C : Capsule n) : Interval (Vec ℝ n) :=
  ⟨fun i => C.c i - (|C.g i| + C.r), fun i => C.c i + (|C.g i| + C.r)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
