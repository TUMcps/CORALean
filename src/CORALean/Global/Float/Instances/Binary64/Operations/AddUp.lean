import CORALean.Global.Float.Instances.Binary64.Operations.NextUp

/-!
# Addition, rounded up

The machine rounds to nearest, which bounds nothing in a stated direction, so
this is the machine's sum followed by one step outward: `nextUp` of a
round-to-nearest result is strictly above the exact value, because the exact
value is never as far as a whole step from the nearest float to it. The price
is one unit in the last place, paid whether or not the machine rounded at all.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def addUp (a b : Float) : Float := nextUp (a + b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
