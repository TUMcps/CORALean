import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# Halving

The one operation both directions agree on: `half` is `Axioms`' assumed
equality, not a rounded primitive.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact on a binary format away from the subnormals, where it is the exponent
alone that moves. `Axioms` assumes the equality and says what the subnormals
cost. -/
def half (a : Float) : Float := a * 0.5

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
