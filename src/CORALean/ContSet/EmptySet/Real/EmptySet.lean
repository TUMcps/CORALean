module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The empty set: the representation

CORA's `emptySet`, a set class of its own rather than a degenerate case of another: `Interval` says
`∅` with a crossed box and `HPolytope` with an unsatisfiable row, each spending data on a fact that
carries none. No fields at all. The dimension is the index and not a field, as
`ContSet (EmptySet n) (Vec ℝ n)` needs it to pin the ambient type, and CORA's `emptySet` carries its
dimension the same way. Real layer only: the representation holds no scalar to round, so a `Float`
copy would be the same type twice.

## References

None: the empty set, a set class of CORA's own with no publication; it holds no data to take from
one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- The empty set in `n` dimensions, carrying nothing else. -/
structure EmptySet (n : ℕ) where

/-- `∅`, whatever it is applied to — there is only one thing it can be. -/
def EmptySet.construct (_ : EmptySet n) : Set (Vec ℝ n) := ∅

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
