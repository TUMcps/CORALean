module

public import CORALean.NN.Layers.Operations.OnePlusExpDown

@[expose] public section

/-!
# What a box must satisfy for softplus

The boxes `softplusEnclosure` brackets softplus on: the sharpness is positive, `expUp` covers the
right end, and `logDown` covers `1 + exp` at the left one.

## Inputs
* `β` – sharpness
* `k` – reduction depth of the exponential
* `nl` – range exponent of the logarithm
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* sharpness is positive and the exponential and logarithm stay in range
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sharpness is positive, `expUp` covers the right end, `logDown` the left. -/
def IsSoftplusBox (β : 𝕋) (k nl : ℕ) (l u : 𝕋) : Prop :=
  0 < toReal β ∧ toReal (mulUp β u) ≤ 2 ^ k / 2 ∧
    toReal (onePlusExpDown k (mulDown β l)) ≤ 2 ^ nl / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
