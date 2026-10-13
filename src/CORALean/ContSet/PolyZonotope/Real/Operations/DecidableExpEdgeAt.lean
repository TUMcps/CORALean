import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt

/-!
# `ExpEdgeAt` decides

Split out of `ExpEdgeAt.lean` (issue #62): an instance is found by type class
search wherever `ExpEdgeAt` appears in an `if` or a `Decidable`-bound
argument, which is a use outside the declaring file even though no other file
ever names it — `DecidableExpEdge.lean`'s own instance search reaches here to
build `ExpEdge`'s.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ======================================  MAIN INSTANCE  ======================================= --

/-- The condition decides: it reads only the exponent matrix, and each clause is
ℕ arithmetic or a bounded quantifier. -/
instance PolyZonotope.instDecidableExpEdgeAt {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ)
    (k₀ : Fin p) (i j : Fin h) : Decidable (PolyZonotope.ExpEdgeAt E η k₀ i j) := by
  unfold PolyZonotope.ExpEdgeAt
  infer_instance

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
