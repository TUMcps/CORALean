import CORALean.Global.Float.FloatOps

/-!
# Bringing a slope into `[0, 1]`

ReLU's slope is a precision knob and never a correctness condition: any value in `[0, 1]` is
sound, the error being measured against the value stored. So an unverified candidate — a secant
rounded whichever way, or a caller's own guess — is brought into range with `minimum` and
`maximum`, both exact, which needs no rounding axiom and no decidable order on ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Any candidate becomes a legal slope. -/
def clampUnit (c : 𝕋) : 𝕋 := maximum zero (minimum one c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
