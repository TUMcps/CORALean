import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.zeroMonomials`

The monomials of the constraint generators at the factors `0`: `1` for an exponent column that is
zero, `0` otherwise.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.zeroMonomials (cPZ : ConPolyZono 𝕋 n) : Vec 𝕋 cPZ.s := fun k =>
  if ∀ l, cPZ.EC l k = 0 then one else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
