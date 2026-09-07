import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.Interval.Real.Operations.OfBounds
import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds

/-!
# A halfspace description as a box

CORA's `interval(polytope)` on a halfspace description, which is `2n` linear
programs. The certificates are the caller's — from `boxOfDual` if they come from
a solver's dual solution, from anywhere else otherwise — and the box is read off
their values.

The only conversion here whose cost is not the enclosure but the bounds: the box
is exact as soon as every certificate is tight.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

def HPolytope.interval (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Interval (Vec ℝ n) :=
  Interval.ofBounds up lo


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.interval_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.interval up lo).construct :=
  Interval.subset_ofBounds up lo

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
