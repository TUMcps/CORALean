import CORALean.ContSet.ContSet.Theorems.DependencyPreservingChain
import CORALean.ContSet.ContSet.Theorems.DependencyPreservingComp
import CORALean.ContSet.ContSet.Theorems.HausdorffDistAddLe
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEnclSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint
import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff

/-!
# What the set interface's classes and definitions give together

`smul_mem_linComb_ofPoint`: `LinComb` and `OfPoint` together already give the segment from the
origin to a point, so no class needs a `segment` field.

`DependencyPreserving.comp` and `.chain` are the closure properties a parameterized
representation is judged by: composing two dependency-preserving operations keeps the property,
and a whole loop of them keeps it too, which is what carries a subset of the initial parameters
through to a subset of the result.

Then `minkowskiDiff`, whose elementary theory lives here rather than beside the definition: the
Galois connection `X ⊆ minkowskiDiff S T ↔ X + T ⊆ S` and its counit, monotonicity in each
argument, and — the point of the whole group — `minkowskiDiff_inner_of_outer`, which turns an
outer approximation with a bounded error set into an inner approximation of the exact set.
Everything else running inner here starts from a computed Minkowski difference; this is the
only route from an enclosure, and what an inner reachability algorithm would be built on.
`minkowskiDiff_add_subset_add` and `minkowskiDiff_encl_subset_add` are Althoff's Prop. 3 and
Prop. 4: adding a set to a difference stays inside the difference of the enlarged minuend.

`hausdorffDist_add_le` is the one distance here rather than an inclusion: adding the same
compact set to both sides can only bring them together, which is what lets an order reduction
be priced on the part it actually reduces.
-/
