import CORALean.ContSet.ConZonotope.Real.Cost.Map
import CORALean.ContSet.ConZonotope.Real.Cost.Mtimes
import CORALean.ContSet.ConZonotope.Real.Cost.Reduce

/-!
# What running `ConZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Three operations, and the omission is the point. `map`, `mtimes` and `reduce`
are counted because none of them builds a constraint: the first two carry `P`
over as the field it already is, and `reduce` drops to the enclosing zonotope
and reduces that, so its count is `Zonotope`'s.

`plus`, `and`, `linComb` and `mtimesIntervalMat` are **not** counted, and not
because the work is hard to read off. `HPolytope` stores a row as a linear
functional `α →ₗ[ℝ] ℝ`, so what `comap`, `and` and `halfScaled` cost depends on
whether a row is a dense vector or a composition held unevaluated — which the
definition does not fix and this model cannot guess. A number here would be a
guess presented as a bound, and would compose into every algorithm over
constrained zonotopes. `HPolytope` needs a cost model of its own first.

`ofPoint` and `ofMat` are left out as `Zonotope`'s constructors are: they place
data rather than compute it.
-/
