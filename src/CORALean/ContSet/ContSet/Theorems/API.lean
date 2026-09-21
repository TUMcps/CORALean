import CORALean.ContSet.ContSet.Theorems.DependencyPreservingChain
import CORALean.ContSet.ContSet.Theorems.DependencyPreservingComp
import CORALean.ContSet.ContSet.Theorems.HausdorffDistAddLe
import CORALean.ContSet.ContSet.Theorems.HausdorffDistImageLe
import CORALean.ContSet.ContSet.Theorems.HausdorffDistMulVecLinAddLe
import CORALean.ContSet.ContSet.Theorems.IsCompactSegments
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEnclSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEqIInter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
import CORALean.ContSet.ContSet.Theorems.SegmentsMinkowskiDiffSubset
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint
import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff

/-!
# What the set interface's classes and definitions give together

`smul_mem_linComb_ofPoint`: `LinComb` and `OfPoint` together already give the segment from the
origin to a point, so no class needs a `segment` field.

`DependencyPreserving.comp` and `.chain` are the closure properties a parameterized representation
is judged by: composing two dependency-preserving operations keeps the property, and a whole loop
of them keeps it too, which carries a subset of the initial parameters through to the result.

Then `minkowskiDiff`, whose elementary theory lives here rather than beside the definition: the
Galois connection `X ⊆ minkowskiDiff S T ↔ X + T ⊆ S` and its counit, monotonicity in each argument,
and — the point of the whole group — `minkowskiDiff_inner_of_outer`, which turns an outer
approximation with a bounded error set into an inner approximation of the exact set, what
an inner reachability algorithm is built on. Althoff's Prop. 3 and Prop. 4 are
`minkowskiDiff_add_subset_add` and `minkowskiDiff_encl_subset_add`, his Lemma 1
`minkowskiDiff_eq_iInter`, his Thm. 1's recursion step `minkowskiDiff_add_assoc`; and
`segments_minkowskiDiff_subset` is Wetzlinger and Althoff's Lemma 1.

`hausdorffDist_add_le`, `hausdorffDist_image_le` and `hausdorffDist_mulVecLin_add_le` are the
three distances here rather than inclusions: adding the same compact set to both sides, moving two
sets through a continuous linear map, or perturbing a linear image by another matrix, can each
only bring the two sides together — the last is Wetzlinger et al.'s Prop. 10, cited in its file.
`isCompact_segments` lets such a distance be read back as a witness.
-/
