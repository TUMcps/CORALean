module

public import CORALean.ContSet.Conversion.Float.Interfaces
public import CORALean.ContSet.Conversion.Float.Operations.API
public import CORALean.ContSet.Conversion.Float.Theorems.API
public import CORALean.ContSet.Conversion.Float.Instances

/-!
# Conversions over a floating-point scalar, collected

Every ordered pair the exact layer has, bar the polynomial zonotope's, which
reaches a box and comes back exactly, the box riding in `err`. Where the
rounding goes elsewhere differs by pair, and is the interesting part.

A box reaching a zonotope measures its radius *from the center actually stored*,
upward on both sides, so half a rounded width never leaves an edge short. A
zonotope reaching halfspaces bounds each generator's contribution by the larger
of its rounded-up dot product and its negated rounded-down one. A zonotope
reaching its corners stores the rounded-down corner and charges the gap to the box.

A halfspace description reaching a constrained zonotope is the only genuinely
different problem: a rounded constraint says something *other* than the
original, so the composed rows are widened by `radius (matMulDiff …)`, the most
a coefficient vector in the unit box can turn that entrywise gap into. Several
pairs round nowhere, and the two ellipsoid pairs are where a square root would
have been: a proposed row length per coordinate one way, a proposed `√n` the
other, each checked by a multiplication and neither trusted.

`IntervalOuter` and `OfInterval` carry `𝕋` as an `outParam`, so a
caller still writes only `IntervalOuter S`. `ConZonotope.vPolytopeBox` goes
through a box, vertex enumeration needing an equality test on reals; `Taylm` reaches a box too.
-/
