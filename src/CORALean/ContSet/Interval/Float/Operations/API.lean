import CORALean.ContSet.Interval.Float.Operations.BoundDot
import CORALean.ContSet.Interval.Float.Operations.BoundNegProj
import CORALean.ContSet.Interval.Float.Operations.BoundProj
import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.Intersection
import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Interval.Float.Operations.MinkDiff
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.NonemptyHull
import CORALean.ContSet.Interval.Float.Operations.OfBounds
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.Interval.Float.Operations.Uminus
import CORALean.ContSet.Interval.Float.Operations.Uplus
import CORALean.ContSet.Interval.Float.Operations.Minus
import CORALean.ContSet.Interval.Float.Operations.Infimum
import CORALean.ContSet.Interval.Float.Operations.Supremum
import CORALean.ContSet.Interval.Float.Operations.Or
import CORALean.ContSet.Interval.Float.Operations.ConvHull
import CORALean.ContSet.Interval.Float.Operations.EnclosePoints
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Interval.Float.Operations.Abs
import CORALean.ContSet.Interval.Float.Operations.Empty
import CORALean.ContSet.Interval.Float.Operations.Exp
import CORALean.ContSet.Interval.Float.Operations.Le
import CORALean.ContSet.Interval.Float.Operations.Lt
import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim
import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.Interval.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Interval.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Interval.Float.Operations.Times
import CORALean.ContSet.Interval.Float.Operations.IsFullDim

/-!
# What `Interval` computes

CORA's three operations, the two box constructors every float representation
pays its rounding into, the degenerate box a bias is added as, and the
interval-matrix chain `expIntervalEnclosure` needs: `matMul`, `matPow`, `smul`
and `matPlus`.

The same nine (`uminus`, `uplus`, `minus`, `infimum`, `supremum`, `or`, `convHull_`,
`enclosePoints`, `origin`); only `minus` rounds, `subDown` and `subUp`.

The same eleven: `le`, `lt`, `empty`, three `representsa_*` tests, `exp`, `abs`, `times`, `project`
and `projectHighDim_`. Only `exp` and `times` round.
-/
