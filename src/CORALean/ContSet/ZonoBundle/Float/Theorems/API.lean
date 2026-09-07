import CORALean.ContSet.ZonoBundle.Float.Theorems.AndExact
import CORALean.ContSet.ZonoBundle.Float.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.LinCombOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.ReindexExact
import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOrder

/-!
# What a float zonotope bundle guarantees, collected

Stated over the same sets of real points as the exact layer states them, each
member's rounding already inside its own `construct`. `and` and `reindex` are
exact; `plus`, `linComb` and `mtimes` are enclosures, the pairwise or
componentwise ones the exact layer had plus what the members rounded.

`reduce_outer` holds at any choice of survivors, and `reduce_order_le` needs no
`0 < o`, unlike `Zonotope.reduceCombastel_order_le`: a bundle of `k = 0` is
`univ`, which encloses anything. `reindex_exact` is where `k = 0` costs
something instead — it is why `Set.image_iInter` is taken at a bijection.
-/
