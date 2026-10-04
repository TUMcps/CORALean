import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestGenOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitDepFactorOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ResolveOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetCoefMem
import CORALean.ContSet.PolyZonotope.Float.Theorems.IsequalSound
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetCoefMem
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusH
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ExactPlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesH
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit
import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepIdem
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumMask
import CORALean.ContSet.PolyZonotope.Float.Theorems.SupportBoundLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.ZeroMemDependentErr
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.PolyZonotope.Float.Theorems.CentreMemConstruct
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombH
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombNominalAt
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapENominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.NoIndepSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPolyOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByH
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsDroppedLeDropRadius
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardDependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceDependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOrder
import CORALean.ContSet.PolyZonotope.Float.Theorems.MergedGenGap
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpEvenOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpMultiOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpMidOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpGreedyOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.IsCompact
import CORALean.ContSet.PolyZonotope.Float.Theorems.OriginExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.PadBackExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReindexExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.RestructureOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ProjectOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CartProdExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.BlockPadLeftNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.BlockPadRightNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.StackOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RmIdConstruct
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReplaceIdExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.OnlyIdPoint
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.OnlyIdOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReplaceIdSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.RmIdSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumErrMem
import CORALean.ContSet.PolyZonotope.Float.Theorems.BoxOutOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.OuterApproxOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.PartZonotopeNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.PartZonotopeOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.PolygonOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.JacobianOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitOuter

/-!
# What `PolyZonotope` guarantees

The exact layer's `plus`, `linComb`, `map` and `quadMap` read as enclosures. `plus`, `linComb`
and `mtimes` keep their ℝ counts, rounding going into the error box; `dependent_nominal` moves
the other way, trading the box for generators so `quadMap` has a box-free set to work on.

`mul_outer` encloses the exact product over shared factors, its input the two *nominal* sets,
reached by running `dependent` once; `evalPoly_outer` prices the chain of `mul`s Horner runs.

`reduce_outer` holds at every pair of partitions, which is what lets the ranking be a heuristic
— and what lets it be computed at all here. It goes through `compact_outer`, so the order
`reduce_order_le` bounds counts distinct monomials, as over ℝ, and that is what keeps a
reachability loop's representation from growing a box per step.

`relaxExp_outer` reads the exact layer's drift bound at the stored columns, the two roundings
it makes being the only difference between the layers; `relaxExpEven_outer` the same with a
third for the centre it shifts, `relaxExpMid_outer` the same three at any parity, and
`relaxExpMulti_outer` the same two at any two generators. `mergedGen_gap` is the column all
four store alike. `relaxExpGreedy_outer` composes them, at every selection and step count.

`mem_generatorError` is the one that answers the question the representation
raises — what a monomial costs a float layer — and its docstring is where that
is argued. `MemNominalSet` is how each of them reads the nominal half of a point.
-/
