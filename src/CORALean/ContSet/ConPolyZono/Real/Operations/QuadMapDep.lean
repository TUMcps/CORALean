module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG

@[expose] public section

/-!
# `ConPolyZono.quadMapDep`

The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. Touches the centre, generators and exponent matrix
of the enclosing polynomial zonotope; the constraint system reads none of
those, so `A`, `b` and `EC` pass through untouched.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. -/
def ConPolyZono.quadMapDep (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) where
  p := cPZ.p
  h := (cPZ.h + 1) * (cPZ.h + 1)
  q := 0
  m := cPZ.m
  s := cPZ.s
  c := 0
  G := PolyZonotope.quadMapG Q cPZ.polyZonotope
  E := PolyZonotope.quadMapE cPZ.polyZonotope
  GI := Fin.elim0
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
