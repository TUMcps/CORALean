module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact

@[expose] public section

/-!
# A zonotope bundle is bounded

CORA's `isBounded` is `true`, for a bundle of at least one zonotope; `isCompact_construct`
needs `0 < k` as the empty family denotes the whole space.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isBounded_construct {zB : ZonoBundle α} (h : 0 < zB.k) :
    Bornology.IsBounded zB.construct :=
  (ZonoBundle.isCompact_construct h).isBounded

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
