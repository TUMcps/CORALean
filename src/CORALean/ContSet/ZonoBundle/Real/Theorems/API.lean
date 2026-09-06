import CORALean.ContSet.ZonoBundle.Real.Theorems.AndExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact

/-!
# What a zonotope bundle guarantees, collected

`and` exactly, `plus` and `mtimes` as enclosures, and convexity unconditionally.
`isCompact_construct` is a plain theorem at `0 < B.k`, never a `CompactSet`
instance: `ZonoBundle.lean`'s docstring says why `k = 0` rules that out.
-/
