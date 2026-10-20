module

public import CORALean.NN.Layers.Operations.SampleDevUp
public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# The fallback bracket's upper end

The same fallback from above.

## Inputs
* `E` – enclosure of the activation
* `c` – fit coefficients
* `M` – derivative bound
* `l` – lower end of the interval
* `u` – upper end of the interval

## Output
* upper end of the coarse bracket on the fit's error
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sample at the left end and the whole width as the spacing, from above. -/
def coarseHi (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (M l u : 𝕋) : 𝕋 :=
  sampleHi (fun _ : Fin 1 => sampleDevUp E c l) M (subUp u l)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
