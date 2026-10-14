module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope — the construction

`ConPolyZono.polyZonotope` is the construction; `ConPolyZono_to_PolyZonotope` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
