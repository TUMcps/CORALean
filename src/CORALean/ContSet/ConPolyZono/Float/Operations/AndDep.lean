import CORALean.ContSet.ConPolyZono.Float.Operations.AndA
import CORALean.ContSet.ConPolyZono.Float.Operations.AndB
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.andDep`

Sound where both independent blocks are empty; `and` arranges that. Keeps
`cPZ₁`'s error box and only `cPZ₁`'s generator block: the point it denotes is
`y₁ + e₁`, and `cPZ₂` enters through the constraint system alone, its generator
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
def ConPolyZono.andDep (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := 0
  m := cPZ₁.m + cPZ₂.m + n
  s := cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)
  c := cPZ₁.c
  G := fun i => Fin.append (cPZ₁.G i) fun _ => zero
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := fun _ => Fin.elim0
  A := ConPolyZono.andA cPZ₁ cPZ₂
  b := ConPolyZono.andB cPZ₁ cPZ₂
  EC := Real.ConPolyZono.appendE (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC)
          (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)
  err := cPZ₁.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
