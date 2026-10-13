module

public import CORALean.ContSet.VPolytope.Real.Operations.ConvHull

@[expose] public section

/-!
# `VPolytope.or`

CORA's `@polytope/or`, whose whole body is `convHull_(P,S,varargin{:})`: the union is enclosed by
the convex hull.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.or {α : Type} (P Q : VPolytope α) : VPolytope α :=
  P.convHull Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
