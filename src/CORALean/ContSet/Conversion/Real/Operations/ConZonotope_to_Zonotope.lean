module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# Dropping the constraints — the construction

`ConZonotope.zonotope` is the construction; `ConZonotope_to_Zonotope` states and proves what it
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

def ConZonotope.zonotope (cZ : ConZonotope α) : Zonotope α where
  h := cZ.h
  c := cZ.c
  G := cZ.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
