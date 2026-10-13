import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Division, rounded up

`divDown`'s mirror: negates the shifted dividend twice, turning the floor into
a ceiling exactly as `roundUp` does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def divUp (a b : FixedPoint f) : FixedPoint f :=
  ⟨-(-(a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m)), f⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
