module

public import CORALean.ContSet.Ellipsoid.Real.Complexity.Space.Theorems.API

/-!
# What `Ellipsoid` costs

The size of an operation's result as a function of its operands' — the
generator count `k`, since `Ellipsoid` stores its shape as a generator matrix
rather than a shape matrix precisely so a linear image costs nothing. Each
theorem is `rfl` against the structure instance in `Operations/`.

Center and generator matrix themselves, `q` and `G`, are not counted here: an
equation restating what `Operations/Plus.lean` and `Operations/Mtimes.lean`
already show at the call site is not what issue #5 asks for, any more than
restating `c` and `G` is in `Zonotope`'s directory.

Neither operation multiplies, so there is no `O`-notation candidate here —
`plus_k` adds and `mtimes_k` is the identity.

The number of scalar operations each operation costs is not yet stated here.
-/
