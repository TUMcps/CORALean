import CORALean.ContSet.Conversion.Float.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Float.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid
import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

/-!
# Conversions over a floating-point scalar, collected

Every ordered pair, as in the exact layer, with the rounding paid. Where it goes
differs by pair, and is the interesting part.

A box reaching a zonotope measures its radius *from the centre that was actually
stored*, upward on both sides, so half a rounded width never leaves an edge
short. A zonotope reaching halfspaces bounds each generator's contribution by
the larger of its rounded-up dot product and its negated rounded-down one, the
exact value being free to have either sign. A zonotope reaching its corners
stores the rounded-down corner and charges the gap to the error box, adding the
zonotope's own box rather than replacing it. A halfspace description reaching a
constrained zonotope has the only genuinely different problem: composing its
rows with the generators rounds, and a rounded constraint says something *other*
than the original rather than merely shifting a bound, so the composed rows are
widened by `radius (matMulDiff …)` — the most a coefficient vector in the unit
box can turn that entrywise gap into.

Several round nowhere at all: corners of a box are stored bounds copied, and a
hull becomes a constrained zonotope by renaming its fields.

The two ellipsoid pairs are where a square root would have been, and neither
takes one. A box read off an ellipsoid needs one proposed row length per
coordinate — the pullback of a coordinate direction is a stored row of `G`
outright, so nothing rounds before the check. A box read *as* an ellipsoid needs
one proposed `√n`. Both are checked by a multiplication and neither is trusted.

`ContSet_to_Interval` and `Interval_to_ContSet` are the two pairs whose other
side is a variable, as in the exact layer. Here the box comes back in the scalar
the representation stores, so the class carries `𝕋` as an `outParam` and a
caller still writes only `IntervalOuter S`.

One pair is weaker than its exact counterpart. `ConZonotope.vPolytopeBox` goes
through a box, where the exact layer enumerates the coefficient domain's
vertices; that route asks which rows are tight, which is an equality test on
reals, and deciding it in floating point is verified interval linear algebra
rather than a rounding of this argument.
-/
