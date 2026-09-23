import CORALean.ContSet.HPolytope.Real.Cost.Plus
import CORALean.ContSet.HPolytope.Real.Cost.Mtimes
import CORALean.ContSet.HPolytope.Real.Cost.Intersection

/-!
# What running `HPolytope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Three operations, and each one turns out cheap for the same reason: a halfspace
description stores rows as linear functionals `α →ₗ[ℝ] ℝ`, so `plusOf` and
`mtimesOf` never compute a bound themselves — they take one in as a
`SupportBound` certificate the caller already holds, and only combine or relabel
its `.val`. `intersectionCost` is zero for a different reason, the same one
`HPolytope.intersectionCost`'s own file gives: the constraint lists concatenate.

`comap`, `halfScaled` and `minkDiffOf` are **not** counted, and `ConZonotope`'s
own `Cost/API.lean` already says why: what precomposing or scaling a row costs
depends on whether that row is held as a dense vector or as a composition kept
unevaluated, which the representation does not fix. A number here would be a
guess presented as a bound.

Conversions are left out too. `ofBounds` and `ofPoint` place data rather than
compute it, as `Zonotope`'s constructors do; `vPolytope` and `vPolytopeBox`
are genuinely expensive — `vPolytope`'s own docstring reads `2^m` — and
`VPolytope`'s cost model excludes them for the same reason.
-/
