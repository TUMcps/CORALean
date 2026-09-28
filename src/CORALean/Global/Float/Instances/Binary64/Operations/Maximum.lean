import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# The greater of two floats, NaN-propagating

`Minimum`'s mirror: core's `max a b` is `if a ≤ b then b else a`, which drops a NaN in its
second argument, and this returns it.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def maximum (a b : Float) : Float :=
  -- core's `max` where either comparison holds, which is everywhere but at a NaN; there `a + b`
  if a ≤ b then b else if b < a then a else a + b

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
