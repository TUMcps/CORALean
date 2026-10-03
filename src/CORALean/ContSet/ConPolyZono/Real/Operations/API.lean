import CORALean.ContSet.ConPolyZono.Real.Operations.Isequal
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA
import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionB
import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionALeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionAAgree
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesIntersectionDepIff
import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens
import CORALean.ContSet.ConPolyZono.Real.Operations.ConsCol
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors
import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
import CORALean.ContSet.ConPolyZono.Real.Operations.AbsFactorExtendLeOne
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendRight
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesDependentIff
import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
import CORALean.ContSet.ConPolyZono.Real.Operations.Affine
import CORALean.ContSet.ConPolyZono.Real.Operations.Map
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesMap
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Operations.MtimesEqMap
import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Real.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesPlusIff
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.ConPolyZono.Real.Operations.CartProd
import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
import CORALean.ContSet.ConPolyZono.Real.Operations.ConsPolyZonotope
import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
import CORALean.ContSet.ConPolyZono.Real.Operations.LinComb
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesLinCombIff
import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep
import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
import CORALean.ContSet.ConPolyZono.Real.Operations.OfPoint
import CORALean.ContSet.ConPolyZono.Real.Operations.DropRadius
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceBy
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard
import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdAddCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionMeanSq
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionWithSel
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnionWithSel
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionCrossCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConValue
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsSharedIff
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperA
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperB
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperEC
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsUnionUpperIff
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerEC
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerRight
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionG
import CORALean.ContSet.ConPolyZono.Real.Operations.SumUnionE
import CORALean.ContSet.ConPolyZono.Real.Operations.Union
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConA
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConB
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConE
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConG
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceCon
import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec
import CORALean.ContSet.ConPolyZono.Real.Operations.SumRep
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecBlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullG
import CORALean.ContSet.ConPolyZono.Real.Operations.SumConvHullE
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullA
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullB
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullEC
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsConvHullIff
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHull
import CORALean.ContSet.ConPolyZono.Real.Operations.Project
import CORALean.ContSet.ConPolyZono.Real.Operations.Empty
import CORALean.ContSet.ConPolyZono.Real.Operations.IsFullDimCora
import CORALean.ContSet.ConPolyZono.Real.Operations.LongestFactor
import CORALean.ContSet.ConPolyZono.Real.Operations.Split
import CORALean.ContSet.ConPolyZono.Real.Operations.SplitDepFactor
import CORALean.ContSet.ConPolyZono.Real.Operations.SplitLongestGen

/-!
# What `ConPolyZono` computes

`intersection`, `plus`, `map`, `quadMap` and `compact` exactly, and `dependent`, which
moves the independent block into the dependent one and is what makes both `intersection`
and `quadMap` exact rather than merely sound.

`intersection` is the one to read: everything else a polynomial zonotope already
computes, and this is what the constraints buy.

`compact` is the one that has to know about the sharing: merging is `PolyZonotope`'s at
both blocks, but a factor is dropped only when neither `E` nor `EC` reads it.
`quadMap` carries over from `PolyZonotope` unchanged, and that it does is worth knowing —
a quadratic map reads the generators and the exponent matrix and the constraints read
neither, so they constrain the image as they did the argument.

`PadE` and `AppendE` are the two ways a constraint block is reshaped — widened by factors
it does not read, and set beside another over the same factors — and `Domain` is the pair
`construct` splits into, which compactness reads.

`reduce` ranks both blocks as one and boxes what it drops; `getSubset` reweights one
factor at both, and `reduceCon` spends generators to buy a constraint back. The two
largest constructions are `union`, two fresh factors and a row pinning one operand's
block, and `convHull`, `n + 1` weighted copies of `linComb`.
-/
