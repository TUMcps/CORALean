import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `Zonotope.mtimesBox`

What `mtimes` can add beyond the image of its operand's `construct`, computed
in `𝕋` with directed rounding: the centre's rounding gap, bounded the same way
`plusBox`'s is, and the generators' — each entry known only to within
`matMulDiff`'s rounding gap, which `generatorError` turns into a box exactly as
`mtimesResidual` does — together with the result's own error box.

Not an operation `Reduce`-style, for the same reason `plusBox` is not: only
`mtimes`'s own definition can say how far it may overshoot its operand.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre's rounding gap, bounded as `plusBox`'s is, together with what
inexact generators cost — `matMulDiff`'s rounding gap read through
`generatorError` — and the result's own error box. -/
def Zonotope.mtimesBox (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Interval (Vec 𝕋 m) :=
  (⟨fun i => subDown (mulVecDown M Z.c i) (mulVecUp M Z.c i), fun _ => zero⟩ :
      Interval (Vec 𝕋 m)).plus
    ((Zonotope.generatorError (matMulDiff M fun i j => Z.G j i)).plus
      (Zonotope.mtimes M Z).E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
