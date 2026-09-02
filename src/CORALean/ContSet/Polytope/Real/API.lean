import CORALean.ContSet.Polytope.Real.ToH
import CORALean.ContSet.Polytope.Real.ToV

/-!
# Between the two polytope representations

Conversions live here rather than in either representation, so that neither
depends on the other and a file may import just the description it uses.

Vertices to halfspaces is a check per vertex per row, and as tight as the
directions the caller names.

Halfspaces to vertices has no cheap certificate at all: saying that a halfspace
description sits inside a given hull needs that hull's facets, which is the
conversion again. So it goes through a box — `2n` linear programs, then `2ⁿ`
corners — which is sound, exponential either way, and tight only when the
polytope was a box. Enumerating the true vertices is an algorithm with its own
correctness proof, and a caller who has one hands its vertices to `VPolytope`
and proves the enclosure with `subset_toH` in the other direction.
-/
