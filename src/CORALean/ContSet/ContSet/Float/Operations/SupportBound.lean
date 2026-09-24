import CORALean.ContSet.ContSet.Operations.SupportBoundSegments
import CORALean.Global.Float.FloatBound

/-!
# Float bounds across `segments`

The float counterpart of `ContSet.SupportBound`: `segments` is this interface's
own operation, so its bound rule belongs here rather than in `Global`, and the
float layer needs its own file rather than the same one — a `Real` file must not
be able to reach the floating-point scalar.

`maximum` rather than `max`, and nothing rounds: choosing the larger of two
floats introduces no error.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {α : Type} [AddCommGroup α] [Module ℝ α] {S T : Set α} {c : α →ₗ[ℝ] ℝ}


-- =====================================  MAIN DEFINITION  ====================================== --

def FloatBound.segments (u : FloatBound 𝕋 S c) (v : FloatBound 𝕋 T c) :
    FloatBound 𝕋 (segments S T) c where
  val := maximum u.val v.val
  le := by
    have h := (u.toSupportBound.segments v.toSupportBound).le
    rw [toReal_maximum]
    exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
