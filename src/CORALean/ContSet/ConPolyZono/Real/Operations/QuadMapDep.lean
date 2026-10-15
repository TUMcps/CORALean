module

public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG

@[expose] public section

/-!
# `ConPolyZono.quadMapDep`

The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. Touches the center, generators and exponent matrix
of the enclosing polynomial zonotope; the constraint system reads none of
those, so `A`, `b` and `R` pass through untouched.
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
  qI := 0
  m := cPZ.m
  q := cPZ.q
  c := 0
  G := PolyZonotope.quadMapG Q cPZ.polyZonotope
  E := PolyZonotope.quadMapE cPZ.polyZonotope
  GI := Fin.elim0
  A := cPZ.A
  b := cPZ.b
  R := cPZ.R

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
