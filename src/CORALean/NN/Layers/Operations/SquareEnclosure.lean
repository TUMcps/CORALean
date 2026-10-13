import CORALean.NN.Layers.Definitions.Enclosure

/-!
# The square enclosure

`a·a` rounded each way: `x²` at a stored value.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a·a` rounded each way. -/
def squareEnclosure : Enclosure 𝕋 where
  lo a := mulDown a a
  hi a := mulUp a a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
