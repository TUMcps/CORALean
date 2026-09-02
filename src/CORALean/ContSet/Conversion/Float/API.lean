import CORALean.ContSet.Conversion.Float.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Interval_to_ConZonotope
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

The same pairs as the exact layer with the rounding paid, except two.

Where the rounding goes differs by pair, and is the interesting part. A box
reaching a zonotope measures its radius *from the centre that was actually
stored*, upward on both sides, so half a rounded width never leaves an edge
short. A zonotope reaching halfspaces bounds each generator's contribution by
the larger of its rounded-up dot product and its negated rounded-down one, the
exact value being free to have either sign. A zonotope reaching its corners
stores the rounded-down corner and charges the gap to the error box, adding the
zonotope's own box to it rather than replacing it. And several pairs round
nowhere at all: corners of a box are stored bounds copied, and a hull becomes a
constrained zonotope by renaming its fields.

Missing, both for the same kind of reason — an operation this layer does not
have rather than a rounding it cannot afford. A halfspace description reaching a
constrained zonotope needs its rows composed with the generators, which rounds
and so changes what the constraints say; that needs the residual split, not a
rounding mode. A constrained zonotope reaching its vertices needs the exact
`HPolytope.vPolytope`, which asks which rows are tight — an equality test on
reals, and in floating point an algorithm of its own.
-/
