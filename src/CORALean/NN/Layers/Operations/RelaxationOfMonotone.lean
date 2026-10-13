import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Operations.EnclosureMid

/-!
# The relaxation of a monotone function at slope zero

Nothing but monotonicity: the function's range over the box, carrying no slope. Optimal at
slope zero, the range of `σ t - λ t` only widening as `λ` moves away from zero. It needs the
endpoint values handed to it, `FloatOps` having no transcendental function; the offset is the
enclosure's midpoint and the error the larger distance to either end, rounded up.
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

/-- Monotonicity and nothing else: the function's range over the box, at slope zero. -/
def Relaxation.ofMonotone (E : Enclosure 𝕋) : Relaxation 𝕋 where
  slope _ _ := zero
  offset := E.mid
  error l u := maximum (subUp (E.hi u) (E.mid l u)) (subUp (E.mid l u) (E.lo l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
