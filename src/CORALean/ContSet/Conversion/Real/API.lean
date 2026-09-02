import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope

/-!
# Conversions between representations, collected

One file per ordered pair, named for it, and one declaration named for the
target — CORA's convention, where `interval(zonotope)` is how a zonotope becomes
a box.

Conversions live here rather than in either representation because two
representations of equal standing cannot each import the other: `VPolytope`
converting to `HPolytope` inside `VPolytope/` and back inside `HPolytope/` is a
cycle Lean rejects. A pair that needs no file simply has none, and adding one
reorganises nothing.

An operation may still be *implemented* by conversion — `VPolytope.and` goes out
to halfspaces and back — and then it imports these files by exact path, which is
a dependency and not a cycle.
-/
