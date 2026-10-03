import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact

/-!
# `Zonotope.and_`

CORA's `@zonotope/and_` with method `'conZonotope'`: both zonotopes are converted to constrained
zonotopes, intersected exactly, and the result is enclosed by a zonotope, here by dropping the
constraints (`ConZonotope.zonotope`). An outer enclosure, not the intersection: a zonotope is not
closed under intersection. CORA's interval shortcut (both operands boxes, `'exact'` interval
intersection) and the method `'averaging'` are not covered.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.and_ (Z S : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  (Z.conZonotope.intersection S.conZonotope).zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
