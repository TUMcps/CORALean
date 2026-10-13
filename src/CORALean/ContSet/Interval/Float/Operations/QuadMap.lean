module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMap

@[expose] public section

/-!
# `Interval.quadMap`, over a floating-point scalar

CORA's `@interval/quadMap`: the quadratic map of a box, computed as the box of the zonotope
quadratic map of the box's zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.quadMap (Q : Fin m → Mat 𝕋 n n) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) :=
  let Z := I.zonotope
  (Z.quadMap Q).interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
