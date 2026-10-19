module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.convHull`

CORA's `@polytope/convHull_` at two polytopes: the vertices of both, concatenated. CORA computes
the vertices of each operand and compacts the union; the hull of the union of the vertex lists
is the same set. For an empty operand CORA returns the empty polytope, which is not the hull of
the union; this is the hull, so an empty operand contributes nothing.

## Inputs
* `α` – ambient type
* `P` – first polytope
* `Q` – second polytope

## Output
* polytope of both vertex lists
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.convHull {α : Type} (P Q : VPolytope α) : VPolytope α where
  k := P.k + Q.k
  V := Fin.append P.V Q.V

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
