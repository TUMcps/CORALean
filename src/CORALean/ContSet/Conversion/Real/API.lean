module

public import CORALean.ContSet.Conversion.Real.Definitions.API
public import CORALean.ContSet.Conversion.Real.Interfaces
public import CORALean.ContSet.Conversion.Real.Operations.API
public import CORALean.ContSet.Conversion.Real.Theorems.API
public import CORALean.ContSet.Conversion.Real.Instances

/-!
# Conversions between representations, collected

Every ordered pair of `Interval`, `Zonotope`, `HPolytope`, `VPolytope` and
`ConZonotope`, with the declaration named for the target.

`Ellipsoid`, `PolyZonotope` and `ConPolyZono` each route every pair beyond that
quintet through `Zonotope`, the hub every representation reaches — a
composition, not a direct construction, and CORA computes some of those
directly (a minimum-volume enclosure, say). `ConPolyZono`'s own quintet and
`PolyZonotope` route one hop further, through `ConPolyZono.polyZonotope`. That
completes the matrix at 56 ordered pairs among those eight.

`ZonoBundle` now reaches all eight too, both ways, always through `Zonotope`:
out via `ZonoBundle.zonotope i` at a chosen component — a much bigger loss than
the rest, a bundle existing precisely because its intersection is tighter than
any one member — and in via the same `X → Zonotope` leg its `Zonotope` pair
already had, composed with the exact `Zonotope.zonoBundle`. 72 ordered pairs,
among the nine, complete. `SpectraShadow` is only a target: from `Zonotope` and `Interval`.
`LevelSet` is one too, exact from `Ellipsoid`, `HPolytope` and `Interval`.
Where a conversion only encloses: a zonotope reaching halfspaces is exact only on
the caller's directions; a polynomial zonotope's conversions are all enclosures.
`Capsule` reaches every target the box does, through `Capsule.interval`: coarser than CORA's own.
`Taylm` reaches `Interval` (outer), `PolyZonotope`, `ConPolyZono`; is reached exactly from three.
-/
