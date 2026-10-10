import CORALean.ContSet.Capsule.Real.Cost.Plus
import CORALean.ContSet.Capsule.Real.Cost.PlusVec
import CORALean.ContSet.Capsule.Real.Cost.Mtimes
import CORALean.ContSet.Capsule.Real.Cost.MtimesCora
import CORALean.ContSet.Capsule.Real.Cost.Radius
import CORALean.ContSet.Capsule.Real.Cost.ConvHull
import CORALean.ContSet.Capsule.Real.Cost.Enclose
import CORALean.ContSet.Capsule.Real.Cost.SupportBound
import CORALean.ContSet.Capsule.Real.Cost.EnclosePoints

/-!
# What running `Capsule`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/` states that a capsule has no
size to prove anything about; this is the other half, and a capsule is cheap to
compute with: every count is a polynomial in the dimensions, none depends on a
generator or constraint count, there being none. A `sqrt` is priced as one
operation, like a division.

Not counted: the predicates (`containsPoint`, `isIntersecting`, `isequal`,
`empty`, `representsa*`), which decide a `Prop` rather than compute a set;
`volume`, which is `Gamma` and a power, outside a model of `+ - * /`;
`segDist`, an infimum over a set rather than an algorithm; `vertices`; and
`ofPoint`, `project` and `reindex`, which place or read data and are free.
`mtimesCora` takes the eigenvalue as an argument, so computing it is the
caller's.
-/
