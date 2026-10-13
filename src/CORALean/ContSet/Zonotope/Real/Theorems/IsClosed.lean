module

public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# A zonotope is closed

Read off compactness rather than proved directly, because an affine image of a
merely closed set need not be closed. Closedness on its own is what the
integrand of a set-valued integral is asked for.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isClosed_construct (Z : Zonotope α) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
