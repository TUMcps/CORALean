import CORALean.ContSet.Polytope.Real.ToH

/-!
# Between the two polytope representations

Conversions live here rather than in either representation, so that neither
depends on the other and a file may import just the description it uses.

Only the cheap direction so far. Vertices to halfspaces is a check per vertex
per row; halfspaces to vertices is enumeration, and no enclosure of it is
available that a box does not already give.
-/
