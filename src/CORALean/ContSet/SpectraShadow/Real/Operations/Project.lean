module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Map

@[expose] public section

/-!
# `SpectraShadow.project`

CORA's `@spectraShadow/project`: `spectraShadow(SpS.A, SpS.c(dims,:), SpS.G(dims,:))`, the
center and every generator at the chosen coordinates and the inequality untouched. `dims` may
repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the selection
map, and `project_exact` is `map_exact`.

## Inputs
* `S` – spectrahedral shadow
* `dims` – indices indexed by `Fin m`

## Output
* the shadow with center and generators read at the coordinates `dims`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.project (S : SpectraShadow (Vec ℝ n)) (dims : Fin m → Fin n) :
    SpectraShadow (Vec ℝ m) :=
  S.map (LinearMap.funLeft ℝ ℝ dims)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
