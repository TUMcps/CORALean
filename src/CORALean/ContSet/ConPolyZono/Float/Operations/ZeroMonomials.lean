module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.zeroMonomials`

The monomials of the constraint generators at the factors `0`: `1` for an exponent column that is
zero, `0` otherwise.
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

def ConPolyZono.zeroMonomials (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Vec 𝕋 cPZ.s := fun k =>
  if ∀ l, cPZ.EC l k = 0 then one else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
