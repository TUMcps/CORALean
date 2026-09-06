import CORALean.ContSet.Conversion.Real.ConPolyZono_to_ConZonotope
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_HPolytope
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Interval
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_VPolytope
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Zonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.ConZonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_HPolytope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_VPolytope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.HPolytope_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Interval_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Conversion.Real.Interval_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.VPolytope_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle
import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope

/-!
# Conversions between representations, collected

Every ordered pair of `Interval`, `Zonotope`, `HPolytope`, `VPolytope` and
`ConZonotope`, with the declaration named for the target; `ZonoBundle` adds
just the pair against `Zonotope`, both exact.

`Ellipsoid` and `PolyZonotope` both route every pair beyond that quintet through `Zonotope`, the
hub every representation reaches — a composition, not a direct construction, and CORA computes
some of those directly (a minimum-volume enclosure, say), so a later change may tighten one.
`ConPolyZono` now completes the matrix at fourteen pairs: its own quintet and `PolyZonotope` route
the same way, one hop further — dropping the constraints, at `ConPolyZono.polyZonotope`, then the
sharing, at `PolyZonotope.zonotope`, precision lost twice over. The other direction adds an empty
constraint system via the exact `PolyZonotope.conPolyZono`; only `Zonotope`'s pair, composing two
exact legs, is itself exact. `ConZonotope`'s pair predates this row and is direct and exact.

Where a conversion only encloses, the reason is worth knowing. A hull or a
zonotope reaching halfspaces is exact only on the directions the caller names.
A halfspace description reaching a box is `2n` linear programs and no tighter
than its certificates. Anything reaching a zonotope goes through a box, a tighter
enclosure being a fitting problem; and dropping constraints loses exactly those.
A polynomial zonotope's own conversions are all such enclosures, its sets not
being convex, so none is the tightest a direct construction could give.
-/
