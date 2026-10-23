module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Theorems.SubsetOfBounds
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A halfspace description as a box

CORA's `interval(polytope)` on a halfspace description, which is `2n` linear
programs. The certificates are the caller's — from `boxOfDual` if they come from
a solver's dual solution, from anywhere else otherwise — and the box is read off
their values.

The only conversion here whose cost is not the enclosure but the bounds: the box
is exact as soon as every certificate is tight.

## Inputs
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Hypotheses
* none

## Conclusion
* polytope is contained in its interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.interval_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.interval up lo).construct :=
  Interval.subset_ofBounds up lo

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
