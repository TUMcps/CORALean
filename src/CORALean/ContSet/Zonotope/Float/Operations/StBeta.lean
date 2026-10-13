module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.stBeta`

The approximate coefficients of the centres, `H (c₁ - c₂ - e₂)`, with `e₂` the lower corner of
the second error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.stBeta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Vec 𝕋 Z₂.h :=
  fun k => dotDown (H k) fun l => subDown (subDown (Z₁.c l) (Z₂.c l)) (Z₂.E.inf l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
