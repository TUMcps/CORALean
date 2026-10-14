module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

@[expose] public section

/-!
# A zonotope is a constrained one with nothing to satisfy — the construction

`Zonotope.conZonotope` is the construction; `Zonotope_to_ConZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.conZonotope (Z : Zonotope α) : ConZonotope α where
  h := Z.h
  c := Z.c
  G := Z.G
  P := HPolytope.fullspace _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
