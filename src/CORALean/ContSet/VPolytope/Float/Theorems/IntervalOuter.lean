import CORALean.ContSet.VPolytope.Float.Operations.Interval

/-!
# The float `VPolytope.interval` contains the polytope

Off `Interval.subset_ofBounds`, the bounds having been certified where they were
computed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem VPolytope.interval_outer (P : VPolytope 𝕋 n) :
    P.construct ⊆ P.interval.construct :=
  Interval.subset_ofBounds _ _

end CORALean.Float
