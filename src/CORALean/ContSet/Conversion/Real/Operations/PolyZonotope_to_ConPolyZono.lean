module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# A polynomial zonotope as a constrained one
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.conPolyZono (pZ : PolyZonotope α) : ConPolyZono α where
  p := pZ.p
  h := pZ.h
  qI := pZ.q
  m := 0
  q := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := pZ.GI
  A := 0
  b := 0
  R := fun _ => Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
