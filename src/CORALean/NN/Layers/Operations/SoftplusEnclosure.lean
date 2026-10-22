module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Operations.OnePlusExpDown
public import CORALean.Global.Float.Log

@[expose] public section

/-!
# The softplus enclosure

An enclosure of `log(1 + exp(β t)) / β` for a stored sharpness `β`. Below, `logDown` of
`onePlusExpDown` at `β a` rounded down; above, `logUp` of `1 + expUp` at `β a` rounded up; both
divided by `β`, rounded the same way. `k` is the exponential's reduction depth and `nl`, `kl` the
logarithm's. Like `expUp` and `logDown`, the ends bracket the function only where their arguments
are bounded, which `softplusRelaxation_sound` asks of the box.

## Inputs
* `β` – sharpness
* `k` – reduction depth of the exponential
* `nl` – range exponent of the logarithm
* `kl` – reduction depth of the logarithm

## Output
* lower and upper bound of softplus at the stored sharpness
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two ends of `softplus β`, at a stored sharpness. -/
def softplusEnclosure (β : 𝕋) (k nl kl : ℕ) : Enclosure 𝕋 where
  enclose a := ⟨divDown (logDown nl kl (onePlusExpDown k (mulDown β a))) β,
    divUp (logUp nl kl (addUp one (expUp k (mulUp β a)))) β⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
