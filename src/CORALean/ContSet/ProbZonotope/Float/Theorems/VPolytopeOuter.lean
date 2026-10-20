module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains

@[expose] public section

/-!
# `ProbZonotope.vPolytope` contains the mean zonotope

Outer: the corner polytope contains the mean zonotope, the corners rounded outward; the covariance
plays no part.

## Inputs
* `P` – probabilistic zonotope

## Hypotheses
* none

## Conclusion
* `ProbZonotope.vPolytope` contains the mean zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.vPolytope_contains (P : ProbZonotope 𝕋 n) :
    P.Z.construct ⊆ P.vPolytope.construct :=
  Zonotope.vPolytope_contains P.Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
