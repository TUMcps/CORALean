module

public import CORALean.ContSet.ZonoBundle.Real.Complexity.Space.Theorems.API

/-!
# What `ZonoBundle` costs

The size of an operation's result as a function of its operands' — the bundle
size `k`, since that is the count `intersection`, `plus`, `linComb`, `mtimes` and
`mtimesMatZonotope` each move. Each equality is `rfl` against the structure
instance in `Operations/`.

A second-order count is worth stating too: the generator count of each
component zonotope. It comes out cleanly for `plus`, `linComb`, `mtimes` and
`mtimesMatZonotope`, in the same files as `k`, by the corresponding `Zonotope`
theorem. It does
not for `intersection`: every component passes through `Fin.append` unchanged, which
says nothing `Operations/Intersection.lean` does not already say at the call site.

`plus_k_isBigO` puts `plus`'s quadratic bundle size in `O`-notation.

The number of scalar operations each operation costs is not yet stated here.
-/
