import CORALean.ContSet.ConPolyZono.Float.Operations.AndA
import CORALean.ContSet.ConPolyZono.Float.Operations.AndB
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.andDep`

Sound where both independent blocks are empty; `and` arranges that. Keeps
`C₁`'s error box and only `C₁`'s generator block: the point it denotes is
`y₁ + e₁`, and `C₂` enters through the constraint system alone, its generator
columns kept at `zero` so the agreement rows can read the second point.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Sound where both independent blocks are empty; `and` arranges that. -/
def ConPolyZono.andDep (C₁ C₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := 0
  m := C₁.m + C₂.m + n
  s := C₁.s + C₂.s + (C₁.h + C₂.h)
  c := C₁.c
  G := fun i => Fin.append (C₁.G i) fun _ => zero
  E := Real.PolyZonotope.plusE C₁.E C₂.E
  GI := fun _ => Fin.elim0
  A := ConPolyZono.andA C₁ C₂
  b := ConPolyZono.andB C₁ C₂
  EC := Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
          (Real.PolyZonotope.plusE C₁.E C₂.E)
  err := C₁.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
