import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge

/-!
# `ExpEdge` decides

Split out of `ExpEdge.lean` (issue #62): read by `Operations/ExpGreedySel.lean`'s
`if PolyZonotope.ExpEdge E η ij.1 ij.2 then`, which elaborates only because
type class search reaches this instance — a use outside the file even though
nothing names it.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- An edge decides: finitely many indices, each of which decides. -/
instance PolyZonotope.instDecidableExpEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ)
    (i j : Fin h) : Decidable (PolyZonotope.ExpEdge E η i j) := by
  unfold PolyZonotope.ExpEdge
  infer_instance

end CORALean.Real
