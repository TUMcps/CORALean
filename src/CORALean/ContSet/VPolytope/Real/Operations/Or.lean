import CORALean.ContSet.VPolytope.Real.Operations.ConvHull

/-!
# `VPolytope.or`

CORA's `@polytope/or`, whose whole body is `convHull_(P,S,varargin{:})`: the union is enclosed by
the convex hull.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.or {α : Type} (P Q : VPolytope α) : VPolytope α :=
  P.convHull Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
