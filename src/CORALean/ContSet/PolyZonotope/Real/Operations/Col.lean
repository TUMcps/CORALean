import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The exponent column of a generator

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by every step of `compact` that follows, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- The exponent column of generator `i`, which is the whole of what its
monomial is. -/
def PolyZonotope.col {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin p → ℕ :=
  fun k => E k i

end CORALean.Real
