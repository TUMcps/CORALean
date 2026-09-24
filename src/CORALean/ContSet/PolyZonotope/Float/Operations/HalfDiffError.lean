import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# What the sliding generator falls short by

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the sliding generator falls short by, over the whole range of the fresh
factor: the stored value rounds down, so the gap to the upper rounding bounds
it, and `[-1,1]` spreads that gap symmetrically. -/
def PolyZonotope.halfDiffError (a b : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  Interval.symmetric fun i =>
    subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
