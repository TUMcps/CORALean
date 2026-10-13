import CORALean.Global.Float.IntRound
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The derivative bound of `1/x` over the box

`|(1/x)⁽ᴺ⁺¹⁾| = (N+1)! / |x|ᴺ⁺²`, at most `(N+1)! · (1/m)ᴺ⁺²` where `m` is the distance from zero
of the hull of the centre and the range, every factor rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.invBound (m : 𝕋) (N : ℕ) : 𝕋 :=
  mulUp (intUp ((N + 1).factorial : ℤ)) (powUp (divUp one m) (N + 2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
