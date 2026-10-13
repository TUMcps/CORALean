import CORALean.Global.Float.Instances.Binary64.Operations.MulUp

/-!
# Multiplication, rounded down

Negates one argument rather than two: a product changes sign with either
factor, where a sum needs both. Otherwise the reading is `AddDown`'s — the
upward assumption at `-a`, turned around by `toReal_neg`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def mulDown (a b : Float) : Float := -mulUp (-a) b

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
