import CORALean.ContSet.Conversion.Real.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# Conversions between representations, collected

Every ordered pair of `Interval`, `Zonotope`, `HPolytope`, `VPolytope` and
`ConZonotope`, one file each, named for the pair, with the declaration named for
the target — CORA's convention, where `interval(zonotope)` is how a zonotope
becomes a box.

Exact: a box to a zonotope, to halfspaces, to a constrained zonotope; a zonotope
to a constrained zonotope and to its `2ʰ` sign corners; a hull to a constrained
zonotope; a bounded halfspace description to a constrained zonotope and to its
vertices; a constrained zonotope to its vertices.

Enclosing, and each for a reason worth knowing. A hull or a zonotope reaching
halfspaces is exact only on the directions the caller names, facet enumeration
being left outside. A halfspace description reaching a box is `2n` linear
programs and no tighter than its certificates. Anything reaching a zonotope goes
through a box, a tighter zonotope enclosure being a fitting problem rather than a
conversion. And anything leaving a constrained zonotope by dropping its
constraints loses exactly those.

Conversions live here rather than in either representation because two
representations of equal standing cannot each import the other. An operation may
still be implemented by conversion — `VPolytope.and` goes out to halfspaces and
back — and then imports these files by exact path, which is a dependency and not
a cycle.
-/
