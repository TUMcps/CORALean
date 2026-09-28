import CORALean.Global.Float.Instances.Binary64.Operations.InRange

/-!
# Halving

The one operation both directions agree on: `half` is `Axioms`' assumed equality, not a rounded
primitive. It holds while the result is normal, where only the exponent moves; a result below
the normal range would have lost a bit, so `inRange` makes it NaN instead.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact where the result is normal, and NaN where it is not. `0.5` by its bits, see `inRange`.
-/
def half (a : Float) : Float := inRange (a * Float.ofBits 0x3FE0000000000000)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
