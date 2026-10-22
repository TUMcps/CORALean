module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Isequal
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLower
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSelRow
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConRow
public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeCons
public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors
public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.ConPolyZono.Real.Operations.AbsFactorExtendLeOne
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Real.Operations.CartProd
public import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Real.Operations.LinComb
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.ConPolyZono.Real.Operations.OfPoint
public import CORALean.ContSet.ConPolyZono.Real.Operations.DropRadius
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceBy
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard
public import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
public import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionMeanSq
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionWithSel
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionCrossCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionG
public import CORALean.ContSet.ConPolyZono.Real.Operations.SumUnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Union
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceCon
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullG
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHull
public import CORALean.ContSet.ConPolyZono.Real.Operations.Project
public import CORALean.ContSet.ConPolyZono.Real.Operations.Empty
public import CORALean.ContSet.ConPolyZono.Real.Operations.IsFullDimCora
public import CORALean.ContSet.ConPolyZono.Real.Operations.LongestFactor
public import CORALean.ContSet.ConPolyZono.Real.Operations.Split
public import CORALean.ContSet.ConPolyZono.Real.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Real.Operations.SplitLongestGen
public import CORALean.ContSet.ConPolyZono.Real.Operations.ExactPlus
public import CORALean.ContSet.ConPolyZono.Real.Operations.SupportBound
public import CORALean.ContSet.ConPolyZono.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.ConPolyZono.Real.Operations.MinkDiff
public import CORALean.ContSet.ConPolyZono.Real.Operations.Rescale
public import CORALean.ContSet.ConPolyZono.Real.Operations.ExtPolyZonotope
public import CORALean.ContSet.ConPolyZono.Real.Operations.ContainsPoint

/-!
# What `ConPolyZono` computes

`intersection`, `plus`, `map`, `quadMap` and `compact` exactly, and `dependent`, which
moves the independent block into the dependent one and is what makes both `intersection`
and `quadMap` exact rather than merely sound.

`intersection` is the one to read: everything else a polynomial zonotope already
computes, and this is what the constraints buy.

`compact` is the one that has to know about the sharing: merging is `PolyZonotope`'s at
both blocks, but a factor is dropped only when neither `E` nor `R` reads it.
`quadMap` carries over from `PolyZonotope` unchanged, and that it does is worth knowing —
a quadratic map reads the generators and the exponent matrix and the constraints read
neither, so they constrain the image as they did the argument.

`PadE` and `AppendE` are the two ways a constraint block is reshaped — widened by factors
it does not read, and set beside another over the same factors — and `Domain` is the pair
`construct` splits into. `relax` loosens every row by a slack factor: a float set's `b_error`.

`reduce` ranks both blocks as one and boxes what it drops; `getSubset` reweights one
factor at both, and `reduceCon` spends generators to buy a constraint back. The two
largest constructions are `union`, two fresh factors and a row pinning one operand's
block, and `convHull`, `n + 1` weighted copies of `linComb`.
-/
