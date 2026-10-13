module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# The exponent column of a generator

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by every step of `compact` that follows, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent column of generator `i`, which is the whole of what its
monomial is. -/
def PolyZonotope.col {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin p → ℕ :=
  fun k => E k i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
