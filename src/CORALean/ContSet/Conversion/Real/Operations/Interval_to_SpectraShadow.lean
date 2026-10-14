module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A box as a spectrahedral shadow — the construction

`Interval.spectraShadow` is the construction; `Interval_to_SpectraShadow` states and proves what it
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

noncomputable def Interval.spectraShadow (I : Interval (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  I.zonotope.spectraShadow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
