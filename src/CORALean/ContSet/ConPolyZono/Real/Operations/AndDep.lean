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
def ConPolyZono.andDep (C₁ C₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := 0
  m := C₁.m + C₂.m + n
  s := C₁.s + C₂.s + (C₁.h + C₂.h)
  c := C₁.c
  G := Fin.append C₁.G 0
  E := PolyZonotope.plusE C₁.E C₂.E
  GI := Fin.elim0
  A := ConPolyZono.andA C₁ C₂
  b := ConPolyZono.andB C₁ C₂ D
  EC := ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
          (PolyZonotope.plusE C₁.E C₂.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
