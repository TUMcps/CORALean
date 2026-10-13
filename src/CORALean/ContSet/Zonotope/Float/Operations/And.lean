import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.ConZonotope.Float.Operations.Intersection

/-!
# `Zonotope.and_`, over a floating-point scalar

CORA's `@zonotope/and_` with method `'conZonotope'`: the float constrained-zonotope intersection of
the two conversions, enclosed by a zonotope that forgets the constraints. As over ℝ, an outer
enclosure; the interval shortcut and `'averaging'` are not covered.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.and_ (Z S : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  (Z.conZonotope.intersection S.conZonotope).zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
