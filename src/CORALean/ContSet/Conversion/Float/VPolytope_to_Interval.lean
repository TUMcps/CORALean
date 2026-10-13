module

public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Float.Operations.BoundProj
public import CORALean.ContSet.VPolytope.Float.Operations.BoundNegProj
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds

@[expose] public section

/-!
# A hull as a box, over a floating-point scalar

The box around the vertices, widened by the error box. Both bounds come from
`SupportBound`, so nothing is computed here.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.interval (P : VPolytope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  Interval.ofBounds P.boundProj P.boundNegProj

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.interval_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.interval.construct :=
  Interval.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
