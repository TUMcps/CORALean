import CORALean.ContSet.PolyZonotope.Real.API

/-!
# Sparse polynomial zonotopes

Kochdumper and Althoff (2021), and CORA's `polyZonotope`: the first
representation here that is not convex, and the one nonlinear reachability
needs. Its `quadMap` is exact, which is what no convex representation can
manage and what the whole construction is for.

`Real` only so far; the float layer is not written.
-/
