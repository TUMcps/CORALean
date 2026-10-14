module

public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds

@[expose] public section

/-!
# A hull as a box, over a floating-point scalar — the construction

`VPolytope.interval` is the construction; `VPolytope_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.interval (P : VPolytope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  Interval.ofBounds P.boundProj P.boundNegProj

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
