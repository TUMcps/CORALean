module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.eqs`, over a floating-point scalar

CORA's equality constructor. Takes an interval right-hand side, which is where
an equality's rounding goes.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.eqs (Ae : Mat 𝕋 q n) (be : Interval (Vec 𝕋 q)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := q
  Ae := Ae
  be := be

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
