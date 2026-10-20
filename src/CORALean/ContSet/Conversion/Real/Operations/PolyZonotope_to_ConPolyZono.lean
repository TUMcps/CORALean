module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# A polynomial zonotope as a constrained one

## Inputs
* `pZ` – polynomial zonotope

## Output
* constrained polynomial zonotope without constraints
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.conPolyZono (pZ : PolyZonotope α) : ConPolyZono α where
  p := pZ.p
  h := pZ.h
  qI := pZ.q
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := pZ.GI
  cons := ⟨0, 0, 0, fun _ => Fin.elim0, 0, Fin.elim0, Interval.unit pZ.p⟩
  cons_eq i := i.elim0
  cons_dom := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
