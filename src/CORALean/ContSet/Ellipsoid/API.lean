import CORALean.ContSet.Ellipsoid.Real.API

/-!
# Ellipsoids, collected

`Real` only. A float layer would have to round `‖·‖₂` — a square root — outward
into an error box, which is a different problem from the directed rounding of
`+` and `*` every other representation's `Float` layer pays, and nothing asks
for it yet.

Stored as a centre and a generator matrix rather than as CORA's shape matrix
`Q`; `Real.Ellipsoid` says why.
-/
