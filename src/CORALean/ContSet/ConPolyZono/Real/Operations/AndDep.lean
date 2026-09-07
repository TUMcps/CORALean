import CORALean.ContSet.ConPolyZono.Real.Operations.AndA
import CORALean.ContSet.ConPolyZono.Real.Operations.AndB
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.andDep`

Exact where both independent blocks are empty; `and` arranges that. `D` is how
far apart the two points may stand.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact where both independent blocks are empty; `and` arranges that. `D` is
how far apart the two points may stand. -/
def ConPolyZono.andDep (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := 0
  m := cPZ₁.m + cPZ₂.m + n
  s := cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)
  c := cPZ₁.c
  G := Fin.append cPZ₁.G 0
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  A := ConPolyZono.andA cPZ₁ cPZ₂
  b := ConPolyZono.andB cPZ₁ cPZ₂ D
  EC := ConPolyZono.appendE (PolyZonotope.plusE cPZ₁.EC cPZ₂.EC)
          (PolyZonotope.plusE cPZ₁.E cPZ₂.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
