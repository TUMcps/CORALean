module

public import CORALean.NN.Layers.Definitions.Enclosure

@[expose] public section

/-!
# The offset a slope-zero relaxation stores

Any stored value between the enclosure's two ends would be a sound offset — the error is
measured from whichever one is written down — so the midpoint is a precision choice, and its
rounding costs nothing. Halving is exact in a binary format.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset such a relaxation stores, the midpoint of the enclosure's ends. -/
def Enclosure.mid (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 := half (addUp (E.lo l) (E.hi u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
