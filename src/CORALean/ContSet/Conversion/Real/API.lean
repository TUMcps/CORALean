import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
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
`ConZonotope`, one file each, named for the pair, with the declaration named for
the target — CORA's convention, where `interval(zonotope)` is how a zonotope
becomes a box.

The two later arrivals are not paired with all of them, and the gaps differ in
kind.

`Ellipsoid` reaches a box in closed form and tightly, and a zonotope through
that box; a box and a zonotope reach it by the `√k` inflation a Euclidean ball
needs to cover a cube. Its pairs with the two polytopes are missing rather than
impossible.

`PolyZonotope` has four of its ten. Both directions against `Zonotope`, and both
against `Interval` — the latter composed through `Zonotope`, which is why they
are only as tight as that route. The six against `HPolytope`, `VPolytope` and
`ConZonotope` are missing for a reason: a polynomial zonotope is generally not
convex, so a halfspace, vertex or constrained-zonotope description of one is an
enclosure with a precision knob rather than a conversion, and the reverse asks
which factors to invent.

Exact: a box to a zonotope, to halfspaces, to a constrained zonotope; a zonotope
to a constrained zonotope and to its `2ʰ` sign corners; a hull to a constrained
zonotope; a bounded halfspace description to a constrained zonotope and to its
vertices; a constrained zonotope to its vertices; and a zonotope to a polynomial
zonotope, one factor per generator.

Enclosing, and each for a reason worth knowing. A hull or a zonotope reaching
halfspaces is exact only on the directions the caller names, facet enumeration
being left outside. A halfspace description reaching a box is `2n` linear
programs and no tighter than its certificates. Anything reaching a zonotope goes
through a box, a tighter zonotope enclosure being a fitting problem rather than a
conversion. And anything leaving a constrained zonotope by dropping its
constraints loses exactly those, as anything leaving a polynomial zonotope by
freeing its dependent generators loses exactly the sharing between them.

`ConPolyZono` has three. Two pin its definition down: a polynomial zonotope is
one with no constraints, exactly, and a constrained one becomes a polynomial
zonotope by dropping them, which frees the factors from the subvariety the
constraints confined them to. The third is from `ConZonotope`, and it is exact:
that representation cuts its coefficients down with a halfspace description,
inequalities included, and a constrained polynomial zonotope now carries an
interval right-hand side, so an inequality is a row with a free lower bound
rather than a slack factor to invent. Its remaining pairs are the polynomial
zonotope's gaps for the same reason, one non-convexity further along.

`ContSet_to_Interval` and `Interval_to_ContSet` are the two pairs whose other
side is a variable: an algorithm that has to reach a box, or come back from one,
without naming what it is propagating asks for those as classes. Only the
representations that can do it without certificates instantiate them.

Conversions live here rather than in either representation because two
representations of equal standing cannot each import the other. An operation may
still be implemented by conversion — `VPolytope.and` goes out to halfspaces and
back — and then imports these files by exact path, which is a dependency and not
a cycle.
-/
