module

public import CORALean.ContSet.ProbZonotope.Float.Operations.VPolytope

@[expose] public section

/-!
# `ProbZonotope.vPolytope` contains the mean zonotope

Outer: the corner polytope contains the mean zonotope, the corners rounded outward; the covariance
plays no part.
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
