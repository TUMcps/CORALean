module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# `Zonotope.and_`, over a floating-point scalar

CORA's `@zonotope/and_` with method `'conZonotope'`: the float constrained-zonotope intersection of
the two conversions, enclosed by a zonotope that forgets the constraints. As over ℝ, an outer
enclosure; the interval shortcut and `'averaging'` are not covered.

## Inputs
* `Z` – first zonotope
* `S` – second zonotope

## Output
* zonotope enclosing the intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.and_ (Z S : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  (Z.conZonotope.intersection S.conZonotope).zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
