module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_SpectraShadow

@[expose] public section

/-!
# A capsule as a spectrahedral shadow — the construction

`Capsule.spectraShadow` is the construction; `Capsule_to_SpectraShadow` states and proves what it
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

noncomputable def Capsule.spectraShadow (C : Capsule n) : SpectraShadow (Vec ℝ n) :=
  C.interval.spectraShadow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
