import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
import CORALean.ContSet.VPolytope.Float.Operations.BoundProj
import CORALean.ContSet.VPolytope.Float.Operations.BoundNegProj
import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds

/-!
# A hull as a box, over a floating-point scalar

The box around the vertices, widened by the error box. Both bounds come from
`SupportBound`, so nothing is computed here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.interval (P : VPolytope 𝕋 n) : Interval 𝕋 n :=
  Interval.ofBounds P.boundProj P.boundNegProj

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.interval_contains (P : VPolytope 𝕋 n) :
    P.construct ⊆ P.interval.construct :=
  Interval.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
