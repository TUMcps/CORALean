import CORALean.ContSet.ContSet.Theorems.EqConstruct
import CORALean.ContSet.ContSet.Theorems.NeOfConstructNe
import CORALean.ContSet.ContSet.Theorems.DependencyPreservingChain
import CORALean.ContSet.ContSet.Theorems.DependencyPreservingComp
import CORALean.ContSet.ContSet.Theorems.EncloseOuter
import CORALean.ContSet.ContSet.Theorems.EnlargeOuter
import CORALean.ContSet.ContSet.Theorems.EnlargeScalarOuter
import CORALean.ContSet.ContSet.Theorems.ProjectHighDimOuter
import CORALean.ContSet.ContSet.Theorems.ProjectOuter
import CORALean.ContSet.ContSet.Theorems.DecomposeOuter
import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneDot
import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneOuter
import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneFloatOuter
import CORALean.ContSet.ContSet.Theorems.HausdorffDist2MulVecLinAddLe
import CORALean.ContSet.ContSet.Theorems.HausdorffDistAddLe
import CORALean.ContSet.ContSet.Theorems.HausdorffDistImageLe
import CORALean.ContSet.ContSet.Theorems.HausdorffDistMulVecLinAddLe
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct
import CORALean.ContSet.ContSet.Theorems.IsCompactSegments
import CORALean.ContSet.ContSet.Theorems.SegmentsEqConvexJoin
import CORALean.ContSet.ContSet.Theorems.UnionSubsetSegments
import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments
import CORALean.ContSet.ContSet.Theorems.LinCombUnionSubset
import CORALean.ContSet.ContSet.Theorems.LinCombConvexHullSubset
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEnclSubsetAdd
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEqIInter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffNotSubsetOfDiscontinuous
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
import CORALean.ContSet.ContSet.Theorems.MinusFromOuter
import CORALean.ContSet.ContSet.Theorems.MinusOuter
import CORALean.ContSet.ContSet.Theorems.MinusFromScalarOuter
import CORALean.ContSet.ContSet.Theorems.MinusScalarOuter
import CORALean.ContSet.ContSet.Theorems.SegmentsMinkowskiDiffSubset
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint
import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff
import CORALean.ContSet.ContSet.Theorems.TimesOuter
import CORALean.ContSet.ContSet.Theorems.UminusOuter
import CORALean.ContSet.ContSet.Theorems.UplusExact
import CORALean.ContSet.ContSet.Theorems.IsFullDimIffAffineSpan
import CORALean.ContSet.ContSet.Theorems.AddProperties
import CORALean.ContSet.ContSet.Theorems.AddPropertiesCounterexample
import CORALean.ContSet.ContSet.Theorems.ImageLinearMapProperties
import CORALean.ContSet.ContSet.Theorems.InterProperties
import CORALean.ContSet.ContSet.Theorems.InteriorEqEmptyIffForallBall
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffProperties
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffPropertiesCounterexample
import CORALean.ContSet.ContSet.Theorems.ProdProperties
import CORALean.ContSet.ContSet.Theorems.ProdPropertiesCounterexample
import CORALean.ContSet.ContSet.Theorems.PropertyFacts
import CORALean.ContSet.ContSet.Theorems.SegmentsProperties
import CORALean.ContSet.ContSet.Theorems.SegmentsPropertiesCounterexample
import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff

/-!
# What the set interface's classes and definitions give together

`smul_mem_linComb_ofPoint`: `LinComb` and `OfPoint` give the segment from the origin to a point.

`DependencyPreserving.comp` and `.chain` are the closure properties a parameterized representation
is judged by: composing two dependency-preserving operations keeps the property, and a whole loop
of them keeps it too, which carries a subset of the initial parameters through to the result.

Then `minkowskiDiff`, whose elementary theory lives here rather than beside the definition: the
Galois connection `X ⊆ minkowskiDiff S T ↔ X + T ⊆ S` and its counit, monotonicity in each argument,
and — the point of the whole group — `minkowskiDiff_inner_of_outer`, which turns an outer
approximation with a bounded error set into an inner approximation of the exact set, what
an inner reachability algorithm is built on. Althoff's Prop. 3 and Prop. 4 are
`minkowskiDiff_add_subset_add` and `minkowskiDiff_encl_subset_add`, his Lemma 1
`minkowskiDiff_eq_iInter`, his Thm. 1's step `minkowskiDiff_add_assoc`; Wetzlinger and
Althoff's Lemma 1 is `segments_minkowskiDiff_subset`, and with Kulmburg their Remark 1
`minkowskiDiff_not_subset_of_discontinuous`.

`hausdorffDist_add_le`, `hausdorffDist_image_le` and `hausdorffDist_mulVecLin_add_le` are the
three distances here rather than inclusions: adding the same compact set to both sides, moving two
sets through a continuous linear map, or perturbing a linear image by another matrix, can each
only bring the two sides together — the last is Wetzlinger et al.'s Prop. 10, cited in its file.
`isCompact_segments` lets such a distance be read back as a witness.
-/
