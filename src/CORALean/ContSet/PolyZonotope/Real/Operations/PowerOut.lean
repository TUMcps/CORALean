module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PowerExt

@[expose] public section

/-!
# `PolyZonotope.powerOut`

The terms of the powers `1, …, k` of a row once the terms of every factor are added into the
factor's own (`PolyZonotope.powerParts`): CORA's exponent matrix `[E, E^2, …, E^k]` after
`evaluatePolyZonotopeNeuron`, at `f = (· + ·)` on the exponent columns.

## Inputs
* `f` – product of two terms
* `M` – terms of the first power
* `k` – order

## Output
* terms of the powers up to `k`, each power's own after those of the lower ones
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {β : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.powerOut (f : β → β → β) (M : List β) (k : ℕ) : List β :=
  PolyZonotope.powerParts (fun i => (PolyZonotope.powerExt f M i).length)
    (PolyZonotope.powerExt f M) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
