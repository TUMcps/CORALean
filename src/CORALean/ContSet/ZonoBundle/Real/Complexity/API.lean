import CORALean.ContSet.ZonoBundle.Real.Complexity.And
import CORALean.ContSet.ZonoBundle.Real.Complexity.Plus
import CORALean.ContSet.ZonoBundle.Real.Complexity.PlusBigO
import CORALean.ContSet.ZonoBundle.Real.Complexity.Mtimes

/-!
# What `ZonoBundle` costs

The size of an operation's result as a function of its operands' — the bundle
size `k`, since that is the count `and`, `plus` and `mtimes` each move.
Each equality is `rfl` against the structure instance in `Operations/`.

A second-order count is worth stating too: the generator count of each
component zonotope. It comes out cleanly for `plus` and `mtimes`, in the same
files as `k`, by the corresponding `Zonotope` theorem. It does not for `and`:
every component passes through `Fin.append` unchanged, which says nothing
`Operations/And.lean` does not already say at the call site.

`plus_k_isBigO` puts `plus`'s quadratic bundle size in `O`-notation.

The number of scalar operations each operation costs is not yet stated here.
-/
