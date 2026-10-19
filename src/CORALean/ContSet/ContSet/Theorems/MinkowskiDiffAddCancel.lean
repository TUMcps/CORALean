module

public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter

@[expose] public section

/-!
# Adding a set and taking it back off returns the set

[1, Lemma 1(iii)]: `X ⊕ Y ⊖ Y = X`. The inclusion `⊇` holds for any sets; `⊆` is
Rådström's cancellation, through `minkowskiDiff_inner_of_outer` with the sum as its
own outer approximation.

The paper asks `X` and `Y` convex, compact and nonempty. Only `X` convex and closed
and `Y` nonempty and bounded are used; without `Y` nonempty the difference is the
whole space.

## Inputs
* `X` – minuend summand
* `Y` – subtrahend summand

## Hypotheses
* `hY` – `Y` nonempty
* `hYb` – `Y` bounded
* `hXconv` – `X` convex
* `hXcl` – `X` closed

## Conclusion
* `(X + Y) ⊖ Y` equals `X`

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1(iii)]: `(X + Y) ⊖ Y = X` for `X` convex and closed and `Y` nonempty
and bounded. -/
theorem minkowskiDiff_add_cancel {X Y : Set α} (hY : Y.Nonempty)
    (hYb : Bornology.IsBounded Y) (hXconv : Convex ℝ X) (hXcl : IsClosed X) :
    minkowskiDiff (X + Y) Y = X :=
  Set.Subset.antisymm (minkowskiDiff_inner_of_outer hY hYb hXconv hXcl subset_rfl)
    fun _ hx _ hy => Set.add_mem_add hx hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
