module

public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Theorems.API

/-!
# What running `HPolytope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/Space/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Three operations are cheap for one reason: rows are linear functionals, so `plusOf`
and `mtimesOf` take a `SupportBound` certificate in and only relabel its `.val`, and
`intersection` concatenates the constraint lists. None computes much, but each writes its result,
read dense: `mtimesOfCost` and `intersectionCost` are those writes and nothing else.

`comap` and `halfScaled` are counted under a stated reading. What precomposing
or scaling a row costs depends on whether that row is held as a dense vector or
as a composition kept unevaluated, which the representation does not fix. So
`comapCost` takes the price of one row's precomposition as a parameter, and
`halfScaledCost` **reads rows as dense vectors** of the coefficient dimension;
both are exactly as good as that reading. `minkDiffOf` is left out.

Conversions are left out too. `ofBounds` and `ofPoint` place data rather than
compute it, as `Zonotope`'s constructors do, and are not priced here; `vPolytope` and `vPolytopeBox`
are genuinely expensive — `vPolytope`'s own docstring reads `2^m` — and
`VPolytope`'s cost model excludes them for the same reason.
-/
