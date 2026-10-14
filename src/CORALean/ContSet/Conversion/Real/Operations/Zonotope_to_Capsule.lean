module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Capsule

@[expose] public section

/-!
# A zonotope as a capsule — the construction

`Zonotope.capsule` is the construction; `Zonotope_to_Capsule` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.capsule (Z : Zonotope (Vec ℝ n)) : Capsule n :=
  Z.interval.capsule

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
