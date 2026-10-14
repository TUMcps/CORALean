module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Map
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Plus
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.QuadMap
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Intersection

/-!
# What running `ConPolyZono`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/Space/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

`map`, `mtimes` and `plus` cost exactly what their `PolyZonotope` counterparts
do — the constraint system, `A`, `b` and `R`, is untouched by any of the
three, so the extra fields a constrained set carries never enter. `dependent`
is zero, for the same reason `PolyZonotope.dependentCost` is: concatenation,
an identity block and a padded constraint block, nothing computed. `quadMap`
and `intersection` compose from that: the first is `PolyZonotope`'s quadratic
map at the sizes `dependent` leaves, the second the agreement rows'
negations and the bound's arithmetic once both operands are dependent.

`reduce` is **not** counted. It runs `compact` and its own `reduceGirard`, a
distinct Girard ranking with no `Complexity/Space/Reduce.lean` proving how large the
result is — the same gap the issue's own notes record for
`Zonotope.reduceGirard`. `compact` and the `Union*` convex-hull family are left
out for the same reason: no `Complexity/Space/` size to compose against.
-/
