import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.isIntersecting`

CORA's `polygon/isIntersecting_` (`overlaps` of two polyshapes) at two polygons given as convex
pieces: some piece of one meets some piece of the other. Two vertex polytopes meet iff a linear
system in the convex-combination weights is feasible (`VPolytope.inter_nonempty_iff`), which is
what is stated here, a Prop and not a decision procedure (it needs a linear program). CORA's
tolerance and `overlaps` on the boundary representation (R-PG) are not covered.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some pair of pieces has a common convex combination of vertices. -/
def Polygon.isIntersecting (P Q : Polygon) : Prop :=
  ∃ p ∈ P.sets, ∃ q ∈ Q.sets, ∃ (β₁ : Fin p.k → ℝ) (β₂ : Fin q.k → ℝ),
    ∑ j, β₁ j • p.V j = ∑ l, β₂ l • q.V l ∧
      ∑ j, β₁ j = 1 ∧ (∀ j, 0 ≤ β₁ j) ∧ ∑ l, β₂ l = 1 ∧ ∀ l, 0 ≤ β₂ l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
