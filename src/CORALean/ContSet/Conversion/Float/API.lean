import CORALean.ContSet.Conversion.Float.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_VPolytope

/-!
# Conversions over a floating-point scalar, collected

Vertices to halfspaces with the bounds rounded outward, and halfspaces to
vertices through a box.

No float counterpart of the exact `toVPolytope`. That one asks which rows are
tight, which is an equality test on reals; deciding it in floating point means
solving each subsystem with directed rounding and is an algorithm of its own,
not a rounding of this one.
-/
