import CORALean.Float.ContSet.Interval.Interval

/-!
# `Interval.residual`

The box an operation owes when it stores a rounded vector: the intended value
lies in `[lo, hi]` but `stored` was written down, so `[lo - stored, hi - stored]`
covers the difference. Mentions no representation — `Zonotope` builds its error
boxes from this.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Interval.residual (lo hi stored : Vec 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

end CORALean.Float
