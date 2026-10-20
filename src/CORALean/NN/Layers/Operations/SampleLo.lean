module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The sampled range's lower end

CORA's `nnHelper/minMaxDiffOrder` with every step rounded outward: the least sampled value,
dropped by the Lipschitz slack `M · dx` rounded *up*, the one place the bound rounds.

## Inputs
* `gLo` – lower bounds at the sample points
* `M` – derivative bound
* `dx` – grid spacing

## Output
* smallest sampled bound lowered by the slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least sampled value, dropped by the slack rounded up. -/
def sampleLo (gLo : Fin (N + 1) → 𝕋) (M dx : 𝕋) : 𝕋 := subDown (minimumOver gLo) (mulUp M dx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
