import CORALean.ContSet.PolyZonotope.Real.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactGens

/-!
# `PolyZonotope.compact`

CORA's `@polyZonotope/compact_`: equal exponent columns are one monomial and are
added together (`compactGens`), a generator that came out zero is dropped
along with it, and a factor at exponent zero in every remaining column is
dropped as well (`compactFactors`). All three exact.

Without this the generator count is noise — `plus` and `quadMap` grow it while
the set stands still — so `reduce` compacts before it ranks. The order matters
in one direction only — dropping a generator can leave a factor unused, never
the reverse.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.compact (PZ : PolyZonotope α) : PolyZonotope α :=
  PZ.compactGens.compactFactors

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
