import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `ConPolyZono.consPolyZonotope`, over a floating-point scalar

The constraint block read as a `PolyZonotope` over `Vec 𝕋 m`: the columns of `A` as dependent
generators at the exponents `EC`, no centre, no independent generators, an error box that is the
origin. Whatever is done to its generators is then done to the constraint columns.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.consPolyZonotope (cPZ : ConPolyZono 𝕋 n) : PolyZonotope 𝕋 cPZ.m where
  p := cPZ.p
  h := cPZ.s
  q := 0
  c := fun _ => zero
  G := fun l i => cPZ.A i l
  E := cPZ.EC
  GI := Fin.elim0
  err := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
