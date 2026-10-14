module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# A box as a polynomial zonotope — the construction

`Interval.polyZonotope` is the construction; `Interval_to_PolyZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.polyZonotope (I : Interval (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  I.zonotope.polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
