module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.consPolyZonotope`, over a floating-point scalar

The constraint block read as a `PolyZonotope` over `Vec 𝕋 m`: the columns of `A` as dependent
generators at the exponents `R`, no centre, no independent generators, an error box that is the
origin. Whatever is done to its generators is then done to the constraint columns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.consPolyZonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 cPZ.m) where
  p := cPZ.p
  h := cPZ.q
  q := 0
  c := fun _ => zero
  G := fun l i => cPZ.A i l
  E := cPZ.R
  GI := Fin.elim0
  I_error := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
