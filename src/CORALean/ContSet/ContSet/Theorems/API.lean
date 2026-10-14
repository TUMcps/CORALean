module

public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Theorems.DependencyPreservingChain
public import CORALean.ContSet.ContSet.Theorems.DependencyPreservingComp
public import CORALean.ContSet.ContSet.Theorems.EncloseOuter
public import CORALean.ContSet.ContSet.Theorems.IntersectStripSeqOuter
public import CORALean.ContSet.ContSet.Theorems.EnlargeOuter
public import CORALean.ContSet.ContSet.Theorems.EnlargeScalarOuter
public import CORALean.ContSet.ContSet.Theorems.ProjectHighDimOuter
public import CORALean.ContSet.ContSet.Theorems.ProjectOuter
public import CORALean.ContSet.ContSet.Theorems.DecomposeOuter
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneDot
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneOuter
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneFloatOuter
public import CORALean.ContSet.ContSet.Theorems.HausdorffDist2MulVecLinAddLe
public import CORALean.ContSet.ContSet.Theorems.HausdorffDistAddLe
public import CORALean.ContSet.ContSet.Theorems.HausdorffDistImageLe
public import CORALean.ContSet.ContSet.Theorems.HausdorffDistMulVecLinAddLe
public import CORALean.ContSet.ContSet.Theorems.IsCompactSegments
public import CORALean.ContSet.ContSet.Theorems.SegmentsEqConvexJoin
public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSegments
public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments
public import CORALean.ContSet.ContSet.Theorems.LinCombConvexHullSubset
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubset
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAddOfSubset
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEnclSubsetAdd
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffEqIInter
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffImageSubsetImageOfContracting
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffImageSubsetImageOfConvex
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMulVecImageSubsetOfContracting
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMulVecImageSubsetOfConvex
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffNotSubsetOfDiscontinuous
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffSubsetOfContinuous
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffSubsetOfContinuousOfConvex
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddCancel
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
public import CORALean.ContSet.ContSet.Theorems.MinusFromOuter
public import CORALean.ContSet.ContSet.Theorems.MinusOuter
public import CORALean.ContSet.ContSet.Theorems.MinusFromScalarOuter
public import CORALean.ContSet.ContSet.Theorems.MinusScalarOuter
public import CORALean.ContSet.ContSet.Theorems.SegmentsMinkowskiDiffSubset
public import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint
public import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff
public import CORALean.ContSet.ContSet.Theorems.TimesOuter
public import CORALean.ContSet.ContSet.Theorems.UminusOuter
public import CORALean.ContSet.ContSet.Theorems.IsFullDimIffAffineSpan
public import CORALean.ContSet.ContSet.Theorems.AddProperties
public import CORALean.ContSet.ContSet.Theorems.AddPropertiesCounterexample
public import CORALean.ContSet.ContSet.Theorems.ImageLinearMapProperties
public import CORALean.ContSet.ContSet.Theorems.InterProperties
public import CORALean.ContSet.ContSet.Theorems.InteriorEqEmptyIffForallBall
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffProperties
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffPropertiesCounterexample
public import CORALean.ContSet.ContSet.Theorems.ProdProperties
public import CORALean.ContSet.ContSet.Theorems.ProdPropertiesCounterexample
public import CORALean.ContSet.ContSet.Theorems.PropertyFacts
public import CORALean.ContSet.ContSet.Theorems.SegmentsProperties
public import CORALean.ContSet.ContSet.Theorems.SegmentsPropertiesCounterexample
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.ContSet.Theorems.DimReduceOuter
public import CORALean.ContSet.ContSet.Theorems.DimReduceTight
public import CORALean.ContSet.ContSet.Theorems.HyperplaneSliceEq
public import CORALean.ContSet.ContSet.Theorems.SubsetHyperplanePolyhedron
public import CORALean.ContSet.ContSet.Theorems.PolygonExact
public import CORALean.ContSet.ContSet.Theorems.IsGreatestImageConvexHull
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneIntervalFloatOuter
public import CORALean.ContSet.ContSet.Theorems.HyperplanePolyhedronAddSubset
public import CORALean.ContSet.ContSet.Theorems.ExistsHyperplanePolyhedronAddNe

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
