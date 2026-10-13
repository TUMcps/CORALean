module

public import CORALean.Global.Float.Instances.Binary64.Binary64

@[expose] public section

/-!
# The lesser of two floats, NaN-propagating

Core's `min a b` is `if a ≤ b then a else b`, which returns `b` when `a` is NaN, since every
comparison with a NaN is false: a NaN in the first argument would be dropped, and a run that left
the trusted range could end in a number. This returns the NaN instead.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def minimum (a b : Float) : Float :=
  -- core's `min` where either comparison holds, which is everywhere but at a NaN; there `a + b`
  if a ≤ b then a else if b < a then b else a + b

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
