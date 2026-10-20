module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# Representations that denote a convex set

A property, not an operation: nothing is computed, so the class has no data field and instantiating
it costs a representation only the proof it already has.

Separate from `CompactSet`, the two being independent: an `HPolytope` is convex and not compact, and
a polynomial zonotope compact and not convex, so a class demanding both would shut each out of the
half it can supply. Only over a module: convexity needs the scaling and nothing topological. Stated
over what a representation *denotes*, not the representation.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- Everything this representation denotes is convex. What an integral valued in
the set needs, and what makes `linComb` a convex hull. -/
class ConvexSet (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  convex_construct (s : S) : Convex ℝ (construct s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
