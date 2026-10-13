import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
import CORALean.Global.Radstrom

/-!
# An outer approximation minus its own error bound is an inner approximation

Inner statements in the library so far all come from a Minkowski difference
computed directly — `MinkDiff`'s own obligation, and `backReachForall_inner`
propagating it along a run. This is the other source, and the one an algorithm
that only encloses can use: given an error bound — a set `E` with `Ŷ ⊆ Y + E` —
the difference `minkowskiDiff Ŷ E` is an *inner* approximation of `Y`.

The proof is one line on top of two facts: `minkowskiDiff Ŷ E + E ⊆ Ŷ ⊆ Y + E`,
and then `E` cancels by Rådström's law.

`E` is asked only to be nonempty and bounded, which is what the cancellation
uses; a caller holding a convex compact error set — a box, a zonotope — has
both. `Y` must be convex and closed, and that is not a technicality: it is the
exact set the algorithm is about, so the hypothesis says which systems this
answers for.

-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer approximation `Ŷ` of `Y` whose error is bounded by `E` becomes an
inner approximation once `E` is taken back off it. -/
theorem minkowskiDiff_inner_of_outer {Y Ŷ E : Set α} (hE : E.Nonempty)
    (hEb : Bornology.IsBounded E) (hYconv : Convex ℝ Y) (hYcl : IsClosed Y)
    (hOuter : Ŷ ⊆ Y + E) : minkowskiDiff Ŷ E ⊆ Y :=
  radstrom_cancel hE hEb hYconv hYcl ((minkowskiDiff_add_subset Ŷ E).trans hOuter)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
