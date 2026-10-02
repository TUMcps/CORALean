# contSet/@polygon

CORA methods of `contSet/@polygon/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Polygon`, a finite union of convex 2-D polytopes: `SetUnion (VPolytope (Vec ℝ 2))` (`Polygon.Real.Polygon`) and its float analogue (`Polygon.Float.Polygon`). A polygon is built from convex pieces; CORA's `polyshape` boundary lists (holes, regions) need a triangulation, which is not formalized, so the methods that read the boundary or are polygon boolean operations stay `—`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | — | — | polygon boolean operation (intersection of unions is pairwise, but removing overlaps needs the polyshape boundary) |
| `center` | — | — | centroid of the polyshape area |
| `compact_` | — | — | boundary simplification (Douglas-Peucker) |
| `contains_` | proved | [`Polygon.mem_construct_iff`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/MemConstruct.lean) | a point lies in the polygon iff it lies in some piece; no decision procedure (a membership test needs a linear program), and CORA's tolerance, boundary expansion and polygon-in-polygon containment are not covered |
| `convHull_` | proved | [`Polygon.convHull`](../../../src/CORALean/ContSet/Polygon/Real/Operations/ConvHull.lean), [`Polygon.convHull_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ConvHullExact.lean) | at one polygon; exactly the convex hull of the union, a `VPolytope` on the vertices of all pieces; the two-set form is `VPolytope.convHull` at the polytope hull, not given; no float counterpart |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | float | [`Polygon.empty`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Empty.lean), [`Polygon.construct_empty`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/EmptyExact.lean) · float: [`Polygon.empty`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Empty.lean), [`Polygon.construct_empty`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/EmptyExact.lean) |  |
| `enclosePoints` | — | — | CORA returns a non-convex `boundary(points, 0.5)` shape, not the convex hull `Polygon.convHull` gives |
| `expandBoundaries` | — | — | boundary operation |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getHoles` | — | — | reads the polyshape boundary |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `getRegions` | — | — | reads the polyshape boundary |
| `hausdorffDist` | — | — | not given |
| `interval` | float | [`Polygon.interval`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Interval.lean), [`Polygon.interval_contains`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/IntervalContains.lean) · float: [`Polygon.interval`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Interval.lean), [`Polygon.interval_contains`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/IntervalContains.lean) | outer: the hull (`Interval.or`) of the pieces' boxes, which is the tightest box only as a hull of the pieces' tightest boxes |
| `isBounded` | float | [`Polygon.isBounded_construct`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/IsBounded.lean), [`Polygon.isCompact_construct`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/IsCompact.lean) · float: [`Polygon`](../../../src/CORALean/ContSet/Polygon/Float/Polygon.lean), [`Polygon.isCompact_construct`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/IsCompact.lean) | route a — CORA returns `true`; a finite union of polytopes is compact, hence bounded; float boundedness is its compactness |
| `isConvex` | — | — | boundary test |
| `isFullDim` | — | — | CORA counts boundary vertices |
| `isIntersecting_` | — | — | not given |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — | boundary comparison up to collinear points |
| `lift_` | float | [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Project.lean), [`Polygon.project_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ProjectExact.lean) · float: [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Project.lean), [`Polygon.project_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/ProjectOuter.lean) | CORA reduces it to `project` when `length(proj) = N` and throws otherwise: the same declarations as `project`; exact at the real layer, outer at float |
| `linComb` | float | [`Polygon.linComb`](../../../src/CORALean/ContSet/Polygon/Real/Operations/LinComb.lean), [`Polygon.linComb_outer`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/LinCombOuter.lean) · float: [`Polygon.linComb`](../../../src/CORALean/ContSet/Polygon/Float/Operations/LinComb.lean), [`Polygon.linComb_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/LinCombOuter.lean) | outer: pairwise hulls of the pieces, each `VPolytope.linComb`, which is outer |
| `minkDiff` | — | — | a polygon Minkowski difference needs the boundary, not the convex pieces |
| `minus` | — | — | polygon boolean operation on boundaries |
| `mldivide` | — | — | polygon boolean operation on boundaries |
| `mtimes` | float | [`Polygon.mtimes`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Mtimes.lean), [`Polygon.mtimes_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/MtimesExact.lean) · float: [`Polygon.mtimes`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Mtimes.lean), [`Polygon.mtimes_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/MtimesOuter.lean) | at a `2 × 2` matrix; exact at the real layer, outer at float; the scalar case is not given |
| `or` | float | [`Polygon.or`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Or.lean), [`Polygon.or_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/OrExact.lean) · float: [`Polygon.or`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Or.lean), [`Polygon.or_exact`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/OrExact.lean) | the union exactly: the pieces of both, nothing is computed |
| `plus` | float | [`Polygon.plus`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Plus.lean), [`Polygon.plus_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/PlusExact.lean) · float: [`Polygon.plus`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Plus.lean), [`Polygon.plus_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/PlusOuter.lean) | at a polygon; exact at the real layer (pairwise sums of convex pieces), outer at float; the translation by a point is not given |
| `polygon` | float | [`Polygon.ofPieces`](../../../src/CORALean/ContSet/Polygon/Real/Operations/OfPieces.lean), [`Polygon.construct_ofPieces`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ConstructOfPieces.lean) · float: [`Polygon.ofPieces`](../../../src/CORALean/ContSet/Polygon/Float/Operations/OfPieces.lean), [`Polygon.construct_ofPieces`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/ConstructOfPieces.lean) | from convex pieces; CORA's boundary vertex lists (polyshape, holes) need a triangulation, not formalized (see `Polygon.lean`) |
| `polytope` | proved | [`Polygon.convHull`](../../../src/CORALean/ContSet/Polygon/Real/Operations/ConvHull.lean), [`Polygon.convHull_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ConvHullExact.lean) | CORA's `polytope(pgon)` is the polytope on the vertices of `convHull(pgon)`: the same `Polygon.convHull`, a `VPolytope`; no float counterpart |
| `project` | float | [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Project.lean), [`Polygon.project_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ProjectExact.lean) · float: [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Project.lean), [`Polygon.project_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/ProjectOuter.lean) | two coordinates (`V(dims,:)`); the single-coordinate case, which CORA answers with the interval hull, is not given; exact at the real layer, outer at float |
| `projectHighDim_` | float | [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Project.lean), [`Polygon.project_exact`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/ProjectExact.lean) · float: [`Polygon.project`](../../../src/CORALean/ContSet/Polygon/Float/Operations/Project.lean), [`Polygon.project_outer`](../../../src/CORALean/ContSet/Polygon/Float/Theorems/ProjectOuter.lean) | CORA reduces it to `project` at `N = 2` (`dims` of length 2, polygons being two-dimensional): the same declarations; exact at the real layer, outer at float |
| `quadMap` | — | — | not given |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `removeCollinearPoints` | — | — | boundary operation |
| `representsa_` | proved | [`Polygon.representsaEmptySet`](../../../src/CORALean/ContSet/Polygon/Real/Operations/RepresentsaEmptySet.lean), [`Polygon.representsaEmptySet_iff`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/RepresentsaEmptySetIff.lean) | type `'emptySet'` only: empty iff no piece has a vertex; the types `point`, `origin` and `fullspace` are not given, and there is no tolerance; no float counterpart |
| `simplify` | — | — | boundary operation on a polyshape |
| `splitIntoConvexSets` | — | — | boundary operation: the triangulation not formalized |
| `subtract` | — | — | polygon boolean operation on boundaries |
| `supportFunc_` | — | — | not given |
| `times` | — | — | not given |
| `triangulation` | — | — | the conversion from boundary lists to convex pieces, not formalized |
| `vertices_` | proved | [`Polygon.vertices`](../../../src/CORALean/ContSet/Polygon/Real/Operations/Vertices.lean), [`Polygon.convexHull_vertices`](../../../src/CORALean/ContSet/Polygon/Real/Theorems/VerticesHull.lean) | the vertices of the convex pieces, not the boundary vertices of the region CORA returns; the theorem is that their hull is the polygon's (`convexHull_vertices`); no float counterpart |
| `volume_` | — | — | area of a non-convex union needs the boundary (pieces may overlap) |
