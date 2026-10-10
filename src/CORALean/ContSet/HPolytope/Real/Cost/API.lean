import CORALean.ContSet.HPolytope.Real.Cost.Plus
import CORALean.ContSet.HPolytope.Real.Cost.Mtimes
import CORALean.ContSet.HPolytope.Real.Cost.Intersection
import CORALean.ContSet.HPolytope.Real.Cost.Comap
import CORALean.ContSet.HPolytope.Real.Cost.HalfScaled

/-!
# What running `HPolytope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Three operations are cheap for one reason: rows are linear functionals, so `plusOf`
and `mtimesOf` take a `SupportBound` certificate in and only relabel its `.val`,
and `intersectionCost` is zero because the constraint lists concatenate.

`comap` and `halfScaled` are counted under a stated reading. What precomposing
or scaling a row costs depends on whether that row is held as a dense vector or
as a composition kept unevaluated, which the representation does not fix. So
`comapCost` takes the price of one row's precomposition as a parameter, and
`halfScaledCost` **reads rows as dense vectors** of the coefficient dimension;
both are exactly as good as that reading. `minkDiffOf` is left out.

Conversions are left out too. `ofBounds` and `ofPoint` place data rather than
compute it, as `Zonotope`'s constructors do; `vPolytope` and `vPolytopeBox`
are genuinely expensive — `vPolytope`'s own docstring reads `2^m` — and
`VPolytope`'s cost model excludes them for the same reason.
-/
