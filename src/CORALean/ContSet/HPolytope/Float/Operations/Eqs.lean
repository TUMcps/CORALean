module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.eqs`, over a floating-point scalar

CORA's equality constructor. The right-hand side is a point and the error box the origin: an
equality is kept exact, and an operation that must round one keeps it where a certificate pays
the rounding into the error box (`anchorEqs`), and writes it as two inequalities otherwise.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.eqs (Ae : Mat 𝕋 q n) (be : Vec 𝕋 q) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := q
  Ae := Ae
  be := be
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
