module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact

@[expose] public section

/-!
# `Zonotope.and_`

CORA's `@zonotope/and_` with method `'conZonotope'`: both zonotopes are converted to constrained
zonotopes, intersected exactly, and the result is enclosed by a zonotope, here by dropping the
constraints (`ConZonotope.zonotope`). An outer enclosure, not the intersection: a zonotope is not
closed under intersection. CORA's interval shortcut (both operands boxes, `'exact'` interval
intersection) is not covered; the method `'averaging'` is `Zonotope.andAveraging`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.and_ (Z S : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  (Z.conZonotope.intersection S.conZonotope).zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
