module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq

@[expose] public section

/-!
# The coefficient domain of a constrained zonotope is compact

Closed because it is a halfspace description, and bounded because every
coefficient it admits lies in the unit cube, so it is a closed subset of a
compact ball. Stated apart from `isCompact_construct` because the conversion to
a vertex description needs the domain compact and not the set.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [NormedAddCommGroup α] [NormedSpace ℝ α] in
theorem ConZonotope.isCompact_domain (cZ : ConZonotope α) : IsCompact cZ.domain.construct := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 1)
    (HPolytope.isClosed_construct cZ.domain) fun β hβ => ?_
  rw [Zonotope.closedBall_eq]
  exact (ConZonotope.mem_domain_iff.mp hβ).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
