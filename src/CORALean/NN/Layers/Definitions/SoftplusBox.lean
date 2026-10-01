import CORALean.NN.Layers.Operations.OnePlusExpDown

/-!
# What a box must satisfy for softplus

The boxes `softplusEnclosure` brackets softplus on: the sharpness is positive, `expUp` covers the
right end, and `logDown` covers `1 + exp` at the left one.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sharpness is positive, `expUp` covers the right end, `logDown` the left. -/
def SoftplusBox (β : 𝕋) (k nl : ℕ) (l u : 𝕋) : Prop :=
  0 < toReal β ∧ toReal (mulUp β u) ≤ 2 ^ k / 2 ∧
    toReal (onePlusExpDown k (mulDown β l)) ≤ 2 ^ nl / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
