module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AbsorbRounding
public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeCons
public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Operations.CartProd
public import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactorsSpec
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensSpec
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHull
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullG
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Float.Operations.DropRadius
public import CORALean.ContSet.ConPolyZono.Float.Operations.Empty
public import CORALean.ContSet.ConPolyZono.Float.Operations.ExactPlus
public import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
public import CORALean.ContSet.ConPolyZono.Float.Operations.Isequal
public import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb
public import CORALean.ContSet.ConPolyZono.Float.Operations.LongestFactor
public import CORALean.ContSet.ConPolyZono.Float.Operations.Materialise
public import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
public import CORALean.ContSet.ConPolyZono.Float.Operations.MinkDiff
public import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Float.Operations.MtimesResidual
public import CORALean.ContSet.ConPolyZono.Float.Operations.NominalSupportBound
public import CORALean.ContSet.ConPolyZono.Float.Operations.Origin
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.Project
public import CORALean.ContSet.ConPolyZono.Float.Operations.QuadMap
public import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce
public import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceBy
public import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceGirard
public import CORALean.ContSet.ConPolyZono.Float.Operations.Reindex
public import CORALean.ContSet.ConPolyZono.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.ConPolyZono.Float.Operations.Rescale
public import CORALean.ContSet.ConPolyZono.Float.Operations.Split
public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitLongestGen
public import CORALean.ContSet.ConPolyZono.Float.Operations.SupportBound
public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConErr
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLower
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionSelRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpper
public import CORALean.ContSet.ConPolyZono.Float.Operations.ZeroMonomials

/-!
# What `ConPolyZono` computes

`plus`, `linComb` and `mtimes` pay their rounding into the error box and touch the
constraint system only by copying — `plus` and `linComb` place the two matrices
block-diagonally, `mtimes` leaves them alone. `dependent` copies everything and
rounds nothing at all.

`intersection` is the one that computes constraint data, and the one the representation
exists for. It is possible here only because a constraint row records a slack: its agreement
rows have to admit the difference of two nominal points that each carry an error box, so they
were never going to be an equality, and the rounding of the centers rides along inside the same
slack.

`compact` is the operation that pays into both places at once, and the only one
that does: merging generator columns rounds into the error box, merging
constraint columns into the slack `b_error`, and dropping factors into neither.

`reduce` is the one operation computable here and not over ℝ, ranking generators
with a comparator that owes no laws. It pays nothing of its own: the box it adds
rounds outward, and the rounding it does is `compact`'s, which it runs first.
-/
