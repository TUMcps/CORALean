import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The empty set: the representation

CORA's `emptySet`, a set class of its own rather than a degenerate case of
another: `Interval` says `∅` with a crossed box and `HPolytope` with an
unsatisfiable row, each spending data on a fact that carries none — and a
representation whose sets are always nonempty has no such spelling at all.

No fields at all. The dimension is the index and not a field, because that is
what `ContSet (EmptySet n) (Vec ℝ n)` needs to pin the ambient type — CORA's
`emptySet` carries its dimension the same way, since `∅` in one dimension is
not the `∅` an operation in two may be handed.

Real layer only, and not for want of a float one: the representation holds no
scalar to round, so a `Float` copy would be the same type twice.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
