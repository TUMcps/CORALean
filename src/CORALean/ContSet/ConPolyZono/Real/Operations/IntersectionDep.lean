module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA
public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionB
public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

@[expose] public section

/-!
# `ConPolyZono.intersectionDep`

Exact where both independent blocks are empty; `intersection` arranges that. `D` is how
far apart the two points may stand.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact where both independent blocks are empty; `intersection` arranges that. `D` is
how far apart the two points may stand. -/
def ConPolyZono.intersectionDep (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := 0
  m := cPZ₁.m + cPZ₂.m + n
  q := cPZ₁.q + cPZ₂.q + (cPZ₁.h + cPZ₂.h)
  c := cPZ₁.c
  G := Fin.append cPZ₁.G 0
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  A := ConPolyZono.intersectionA cPZ₁ cPZ₂
  b := ConPolyZono.intersectionB cPZ₁ cPZ₂ D
  R := ConPolyZono.appendE (PolyZonotope.plusE cPZ₁.R cPZ₂.R)
          (PolyZonotope.plusE cPZ₁.E cPZ₂.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
