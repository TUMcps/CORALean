module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Interval.Float.Operations.Or

@[expose] public section

/-!
# `VPolytope.convHull`

CORA's `convHull_` of two V-polytopes: the vertex lists side by side, as over ℝ, the two
families appended. Nothing is rounded in the vertices;
the error box is the hull of the two boxes (`Interval.or`), which is what a convex combination of
a point of one operand with a point of the other needs.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.convHull (P Q : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := P.k + Q.k
  V := Fin.append P.V Q.V
  E := P.E.or Q.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
