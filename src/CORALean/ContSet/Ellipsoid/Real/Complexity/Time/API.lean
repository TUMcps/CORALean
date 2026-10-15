module

public import CORALean.ContSet.Ellipsoid.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.Ellipsoid.Real.Complexity.Time.Theorems.API

/-!
# What running `Ellipsoid`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/Space/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Two operations, and the omission is the point: an ellipsoid has no `linComb`,
`reduce` or `intersection`, none of the three being exact or even standard on
this representation. `map` is not counted separately either — its own file
says it *is* `mtimes` at a matrix read off the map, so `mtimesCost` already
covers it.

`supportBound`, `pullback` and `dualVec` are left out as outside this
directory's scope rather than as hard to count — unlike `HPolytope`'s, an
ellipsoid's support value is closed form, no linear program anywhere in it —
because they are not `plus`, `mtimes`, `linComb`, `reduce` or `intersection`,
nor a conversion `map` composes from.
-/
