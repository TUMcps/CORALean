import CORALean.NN.Operations.IdentityDerEnclosure
import CORALean.NN.Definitions.ScalarEncloses

/-!
# `identityDerEnclosure` encloses the derivative of the identity
The derivative is the constant `1`, and `1` reads as `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem identityDerEnclosure_encloses :
    ScalarEncloses (identityDerEnclosure (𝕋 := 𝕋)) (fun _ => 1) :=
  fun _ _ _ _ => by simp [identityDerEnclosure, toReal_one]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
