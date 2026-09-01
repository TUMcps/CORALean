import CORALean.ContSet.Polytope.Theorems.ConvexHull

/-!
# A vertex description is compact, hence closed and bounded

The hull of a finite set. A halfspace description is closed too but need not be
bounded, which is why the two get separate proofs rather than one.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem VPolytope.isCompact_construct (P : VPolytope α) : IsCompact P.construct := by
  rw [VPolytope.construct_eq_convexHull]
  exact Set.Finite.isCompact_convexHull ℝ (Set.finite_range P.V)

theorem VPolytope.isClosed_construct (P : VPolytope α) : IsClosed P.construct :=
  P.isCompact_construct.isClosed

theorem VPolytope.isBounded_construct (P : VPolytope α) : Bornology.IsBounded P.construct :=
  P.isCompact_construct.isBounded

end CORALean.Real
