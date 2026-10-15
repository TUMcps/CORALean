module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Theorems.API

/-!
# What running `ConPolyZono`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/Space/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

`map`, `mtimes` and `plus` cost what their `PolyZonotope` counterparts do, plus the writes of the
constraint system, `A`, `b` and `R`, which the result carries and no operation computes.
`dependent` computes nothing, as `PolyZonotope.dependentCost` does not: it is the writes of a
concatenation, an identity block and a padded constraint block. `quadMap`
and `intersection` compose from that: the first is `PolyZonotope`'s quadratic
map at the sizes `dependent` leaves, the second the agreement rows'
negations and the bound's arithmetic once both operands are dependent.

`reduce` is **not** counted. It runs `compact` and its own `reduceGirard`, a
distinct Girard ranking with no theorem in `Complexity/Space/Theorems/` proving how large the
result is — the same gap the issue's own notes record for
`Zonotope.reduceGirard`. `compact` and the `Union*` convex-hull family are left
out for the same reason: no `Complexity/Space/` size to compose against.
-/
