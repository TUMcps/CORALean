import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope

/-!
# Conversions over a floating-point scalar, collected

The same pairs as the exact layer, with the bounds rounded outward, minus the
one that has no float counterpart: `HPolytope.vPolytope` asks which rows are
tight, which is an equality test on reals. Deciding it in floating point means
solving each subsystem with directed rounding, and is an algorithm of its own
rather than a rounding of this one — so halfspaces reach vertices here only
through a box.
-/
