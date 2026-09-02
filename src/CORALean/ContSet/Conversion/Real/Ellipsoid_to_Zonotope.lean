import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

/-!
# An ellipsoid as a zonotope

Through the box, as everything reaching a zonotope does here: a tighter
zonotope enclosure of an ellipsoid is a fitting problem — how many generators,
pointed which way — rather than a conversion, and CORA leaves that choice to the
caller too.

The box step is tight and the box-to-zonotope step is exact, so all the loss is
in the first, and it is the loss of an axis-aligned enclosure of a rotated set.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.zonotope (E : Ellipsoid n) : Zonotope (Vec ℝ n) :=
  E.interval.zonotope

theorem Ellipsoid.zonotope_outer (E : Ellipsoid n) : E.construct ⊆ E.zonotope.construct :=
  subset_trans E.interval_outer (Interval.subset_zonotope _)

end CORALean.Real
