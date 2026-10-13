import CORALean.ContSet.Polygon.Float.Polygon
import CORALean.ContSet.VPolytope.Float.Operations.LinComb

/-!
# `Polygon.linComb`, over a floating-point scalar

Every pair of pieces combined by the float polytope's own `linComb`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex combinations of every pair of pieces, one from each polygon. -/
def Polygon.linComb (P Q : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨(P.sets ×ˢ Q.sets).map fun pq => (VPolytope.linComb pq.1 pq.2).materialise⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
