module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.columnGap`

A box wide enough for every vertex's rounding at once, a vertex being a column of
CORA's vertex matrix. The operations here store a whole vertex list, and a hull has
no center to move a vertex away from, so one box has to cover all of it — the widest
gap in each coordinate, taken over the vertices.

-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.columnGap {k : ℕ} (lo hi : Fin k → Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  ⟨fun _ => zero, fun i => maximumOver fun l => subUp (hi l i) (lo l i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
