import CORALean.ContSet.ConPolyZono.Float.Operations.Isequal
import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionA
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionB
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
import CORALean.ContSet.ConPolyZono.Float.Operations.Split
import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedColUp
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensGap
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensSpec
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsColUp
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsGap
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsB
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsSpec
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactorsSpec
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb
import CORALean.ContSet.ConPolyZono.Float.Operations.MtimesResidual
import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Float.Operations.DropRadius
import CORALean.ContSet.ConPolyZono.Float.Operations.Project
import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceBy
import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceGirard
import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Float.Operations.Origin
import CORALean.ContSet.ConPolyZono.Float.Operations.Reindex
import CORALean.ContSet.ConPolyZono.Float.Operations.Empty
import CORALean.ContSet.ConPolyZono.Float.Operations.CartProd
import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
import CORALean.ContSet.ConPolyZono.Float.Operations.ConsPolyZonotope
import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
import CORALean.ContSet.ConPolyZono.Float.Operations.UnitBox
import CORALean.ContSet.ConPolyZono.Float.Operations.RescaleStep
import CORALean.ContSet.ConPolyZono.Float.Operations.Rescale
import CORALean.ContSet.ConPolyZono.Float.Operations.LongestFactor
import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
import CORALean.ContSet.ConPolyZono.Float.Operations.SplitLongestGen
import CORALean.ContSet.ConPolyZono.Float.Operations.Centre
import CORALean.ContSet.ConPolyZono.Float.Operations.RepresentsaPoint
import CORALean.ContSet.ConPolyZono.Float.Operations.NominalSupportBound
import CORALean.ContSet.ConPolyZono.Float.Operations.SupportBound
import CORALean.ContSet.ConPolyZono.Float.Operations.MinkDiff
import CORALean.ContSet.ConPolyZono.Float.Operations.ExactPlus
import CORALean.ContSet.ConPolyZono.Float.Operations.QuadMap
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConCoef
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConErr
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperA
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperB
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerA
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerB
import CORALean.ContSet.ConPolyZono.Float.Operations.Union
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullBlkDiag
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullA
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullB
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullG
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHull
import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDim
import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
import CORALean.ContSet.ConPolyZono.Float.Operations.ZeroMonomials

/-!
# What `ConPolyZono` computes

`plus`, `linComb` and `mtimes` pay their rounding into the error box and touch the
constraint system only by copying — `plus` and `linComb` place the two matrices
block-diagonally, `mtimes` leaves them alone. `dependent` copies everything and
rounds nothing at all.

`intersection` is the one that computes constraint data, and the one the representation
exists for. It is possible here only because the right-hand side of a constraint
is an interval: its agreement rows have to admit the difference of two nominal
points that each carry an error box, so they were never going to be an equality,
and the rounding of the centres rides along inside the same interval.

`compact` is the operation that pays into both places at once, and the only one
that does: merging generator columns rounds into the error box, merging
constraint columns into `b`, and dropping factors into neither.

`reduce` is the one operation computable here and not over ℝ, ranking generators
with a comparator that owes no laws. It pays nothing of its own: the box it adds
rounds outward, and the rounding it does is `compact`'s, which it runs first.
-/
