import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint
import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff

/-!
# What the set interface's classes and definitions give together

`smul_mem_linComb_ofPoint`: `LinComb` and `OfPoint` together already give the
segment from the origin to a point, so no class needs a `segment` field.

The rest is `minkowskiDiff`, whose elementary theory lives here rather than
beside the definition: the Galois connection `X ⊆ minkowskiDiff S T ↔ X + T ⊆ S`
and its counit, monotonicity in each argument, and — the point of the whole
group — `minkowskiDiff_inner_of_outer`, which turns an outer approximation with
a bounded error set into an inner approximation of the exact set. Everything
else running inner here starts from a computed Minkowski difference; this is
the only route from an enclosure, and what an inner reachability algorithm
would be built on.
-/
