import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_HPolytope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_VPolytope
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Conversion.Real.Interval_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# Conversions between representations, collected

Every ordered pair of `Interval`, `Zonotope`, `HPolytope`, `VPolytope` and
`ConZonotope`, with the declaration named for the target.

`Ellipsoid` now has all ten: the box pair closed-form and tight both ways, the rest routed
through `Zonotope`, the hub every representation reaches — a composition, not a direct
construction, and CORA computes some of those directly (a minimum-volume enclosure, say), so a
later change may tighten one. `PolyZonotope` has four of its ten — both directions against
`Zonotope`, and both against `Interval` composed through `Zonotope` and only as tight as that
route. The six against the polytopes and `ConZonotope` are missing for a reason: a polynomial
zonotope is generally not convex, so describing one that way is an enclosure with a precision
knob, and the reverse asks which factors to invent. `ConPolyZono` has three, its gaps the same
one step further: a polynomial zonotope is a constrained one with no constraints and
conversely, and the third pair, from `ConZonotope`, is exact because an interval right-hand
side turns an inequality into a row with a free lower bound.

Where a conversion only encloses, the reason is worth knowing. A hull or a
zonotope reaching halfspaces is exact only on the directions the caller names.
A halfspace description reaching a box is `2n` linear programs and no tighter
than its certificates. Anything reaching a zonotope goes through a box, a tighter
enclosure being a fitting problem; and dropping constraints loses exactly those.
-/
