module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.ZonotopeCora
public import CORALean.ContSet.Polygon.Real.Operations.OfPieces
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `PolyZonotope.polygon`

CORA's `@polyZonotope/polygon` for a two-dimensional set: split along the longest generator
`splits` times, refining only the pieces whose polygon touches the boundary of the union so
far, and return the union of the polygons of `zonotope(piece)`, whose vertices are
`vertices_(zonotope(piece))`. A zonotope's vertex hull is the zonotope, so each piece's polygon
is its `vPolytope` (the corners are a superset of the vertices with the same hull).

The rule that picks the pieces to refine reads the vertices of the union's boundary
(`ismembertol` against a `polyshape`), which has no counterpart here: it is the parameter
`pick`, a verdict per round and piece. Every choice gives an enclosure, so the theorem is
for all of them. The shortcuts for an empty set and for a set that is a zonotope are not
modelled; there CORA returns the set itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the zonotopes of the final pieces. -/
noncomputable def PolyZonotope.polygon (pZ : PolyZonotope (Vec ℝ 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : Polygon :=
  Polygon.ofPieces ((pZ.polygonPieces splits pick).map fun q => q.zonotopeCora.vPolytope)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
