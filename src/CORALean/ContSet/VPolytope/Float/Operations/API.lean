module

public import CORALean.ContSet.VPolytope.Float.Operations.MatPolytope
public import CORALean.ContSet.VPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
public import CORALean.ContSet.VPolytope.Float.Operations.MemColumnGap
public import CORALean.ContSet.VPolytope.Float.Operations.PairSum
public import CORALean.ContSet.VPolytope.Float.Operations.Plus
public import CORALean.ContSet.VPolytope.Float.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Float.Operations.LinComb
public import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundProj
public import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundNegProj
public import CORALean.ContSet.VPolytope.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundDot
public import CORALean.ContSet.VPolytope.Float.Operations.Project
public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Float.Operations.Intersection
public import CORALean.ContSet.VPolytope.Float.Operations.IntersectionCut
public import CORALean.ContSet.VPolytope.Float.Operations.EmptySet
public import CORALean.ContSet.VPolytope.Float.Operations.ConvHull
public import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints
public import CORALean.ContSet.VPolytope.Float.Operations.Origin
public import CORALean.ContSet.VPolytope.Float.Operations.CenterBox
public import CORALean.ContSet.VPolytope.Float.Operations.IsFullDimWith
public import CORALean.ContSet.VPolytope.Float.Operations.IsFullDim
public import CORALean.ContSet.VPolytope.Float.Operations.Materialise

/-!
# What the float `VPolytope` computes

The same three the exact layer does. `plus` and `mtimes` round every vertex and
charge the gap to the box, which `ColumnGap` is; `linComb` concatenates and
charges nothing.
-/
