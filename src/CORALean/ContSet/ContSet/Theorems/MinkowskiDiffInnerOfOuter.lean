module

public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
public import CORALean.Global.Radstrom

@[expose] public section

/-!
# An outer approximation minus its own error bound is an inner approximation

Inner statements so far come from a Minkowski difference computed directly. This is the other
source, usable by an algorithm that only encloses: given an error bound `E` with `Ŷ ⊆ Y + E`, the
difference `minkowskiDiff Ŷ E` is an *inner* approximation of `Y`. The proof is `minkowskiDiff Ŷ E +
E ⊆ Ŷ ⊆ Y + E`, then `E` cancels by Rådström's law. `E` is asked only to be nonempty and bounded,
which the cancellation uses; `Y` must be convex and closed, and that is not a technicality: it is
the exact set the algorithm is about, so the hypothesis says which systems this answers for.

## Inputs
* `Y` – set
* `Ŷ` – outer approximation of `Y`
* `E` – error set

## Hypotheses
* `hE` – `E` nonempty
* `hEb` – `E` bounded
* `hYconv` – `Y` convex
* `hYcl` – `Y` closed
* `hOuter` – `Ŷ ⊆ Y + E`

## Conclusion
* `Ŷ ⊖ E` lies in `Y`
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
