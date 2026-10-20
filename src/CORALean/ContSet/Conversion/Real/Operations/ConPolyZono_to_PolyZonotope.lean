module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* polynomial zonotope with the same data, constraints dropped
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.polyZonotope (cPZ : ConPolyZono α) : PolyZonotope α where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
