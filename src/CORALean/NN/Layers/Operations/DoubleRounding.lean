import CORALean.NN.Layers.Definitions.ScaleRounding

/-!
# Doubling, rounded both ways

Multiplication by `2` as self-addition, `addUp x x` and `addDown x x`: exact in any binary
format, and needing no stored value that denotes `2`, which `FloatOps` does not promise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Doubling by self-addition. -/
def doubleRounding : ScaleRounding 𝕋 where
  up x := addUp x x
  down x := addDown x x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
