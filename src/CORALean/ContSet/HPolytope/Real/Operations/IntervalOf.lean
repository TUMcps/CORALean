import CORALean.ContSet.HPolytope.Real.Operations.DualBound
import CORALean.ContSet.Interval.Real.Operations.OfBounds

/-!
# `HPolytope.intervalOf`

CORA's `interval(polytope)`, which is `2n` linear programs. The certificates are
the caller's — from `boundOfDual` if they come from a solver's dual solution,
from anywhere else otherwise — and the box is read off their values.

The one operation here whose cost is not the enclosure but the bounds: the box
is exact as soon as every certificate is tight.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

def HPolytope.intervalOf (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Interval (Vec ℝ n) :=
  Interval.ofBounds up lo

end CORALean.Real
