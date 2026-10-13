import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.isequalPieces`

CORA's `polygon/isequal` compares the boundary vertex lists after `removeCollinearPoints`. On the
region given as convex pieces, a sufficient test for equality is that every piece of each polygon
lies inside a single piece of the other (`Polygon.isequalPieces_sound`). It is one-sided: it
cannot see that a convex piece is covered by several pieces of the other polygon, so it can say
no for equal regions (two halves of a square against the square; not proved here). The
boundary comparison (R-PG) is not formalized.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece of each polygon lies inside one piece of the other. -/
def Polygon.isequalPieces (P Q : Polygon) : Prop :=
  (∀ p ∈ P.sets, ∃ q ∈ Q.sets, VPolytope.construct p ⊆ VPolytope.construct q) ∧
    ∀ q ∈ Q.sets, ∃ p ∈ P.sets, VPolytope.construct q ⊆ VPolytope.construct p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
