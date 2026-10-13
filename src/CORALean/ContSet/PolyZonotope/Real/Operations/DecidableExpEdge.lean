module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdgeAt
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge

@[expose] public section

/-!
# `ExpEdge` decides

Split out of `ExpEdge.lean` (issue #62): read by `Operations/ExpGreedySel.lean`'s
`if PolyZonotope.ExpEdge E η ij.1 ij.2 then`, which elaborates only because
type class search reaches this instance — a use outside the file even though
nothing names it.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ======================================  MAIN INSTANCE  ======================================= --

/-- An edge decides: finitely many indices, each of which decides. -/
instance PolyZonotope.instDecidableExpEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ)
    (i j : Fin h) : Decidable (PolyZonotope.ExpEdge E η i j) := by
  unfold PolyZonotope.ExpEdge
  infer_instance

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
