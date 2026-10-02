import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Interval.Float.Operations.Or

/-!
# `VPolytope.convHull`

CORA's `convHull_` of two V-polytopes: the vertex lists side by side, as over ℝ, where each
vertex list is a matrix and the lists are joined column-wise. Nothing is rounded in the vertices;
the error box is the hull of the two boxes (`Interval.or`), which is what a convex combination of
a point of one operand with a point of the other needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.convHull (P Q : VPolytope 𝕋 n) : VPolytope 𝕋 n where
  k := P.k + Q.k
  V := fun i => Fin.append (P.V i) (Q.V i)
  E := P.E.or Q.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
