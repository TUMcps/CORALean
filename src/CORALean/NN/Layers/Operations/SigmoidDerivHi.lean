import CORALean.NN.Layers.Definitions.Enclosure

/-!
# The sigmoid derivative's upper bound over a box

`σ u · σ(-l)` from above, the product rounding up; an upper bound on a positive value is
positive, so this side needs no floor.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `σ u · σ(-l)` from above. -/
def sigmoidDerivHi (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 :=
  mulUp (E.hi u) (E.hi (neg l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
