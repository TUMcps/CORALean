module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# A zonotope as a polynomial zonotope

## Inputs
* `Z` – zonotope

## Output
* polynomial zonotope of the zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.polyZonotope (Z : Zonotope α) : PolyZonotope α where
  p := Z.h
  h := Z.h
  q := 0
  c := Z.c
  G := Z.G
  E := PolyZonotope.identE Z.h
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
