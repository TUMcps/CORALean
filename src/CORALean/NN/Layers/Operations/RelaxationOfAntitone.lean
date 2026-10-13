module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# The relaxation of an antitone function at slope zero

The mirror of `Relaxation.ofMonotone` for a falling `σ`: over `[l, u]` it stays between its
values at `u` and at `l`, so the offset is the midpoint of the enclosure's lower end at `u` and
upper end at `l`, and the error the larger distance to either, rounded up. The inverse square
root a graph network normalises by is the function it exists for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Antitonicity and nothing else: the function's range over the box, at slope zero. -/
def Relaxation.ofAntitone (E : Enclosure 𝕋) : Relaxation 𝕋 where
  slope _ _ := zero
  offset l u := half (addUp (E.lo u) (E.hi l))
  error l u := maximum (subUp (E.hi l) (half (addUp (E.lo u) (E.hi l))))
    (subUp (half (addUp (E.lo u) (E.hi l))) (E.lo u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
