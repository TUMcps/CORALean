import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.columnGap`

A box wide enough for every column's rounding at once. The operations here store
a whole vertex list, and a hull has no centre to move a vertex away from, so one
box has to cover all of it — the widest gap in each coordinate, taken over the
columns.

-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.columnGap {k : ℕ} (lo hi : Mat 𝕋 n k) : Interval (Vec 𝕋 n) :=
  ⟨fun _ => zero, fun i => maximumOver fun l => subUp (hi i l) (lo i l)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
