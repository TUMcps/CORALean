module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioAt
public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioStep
public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatio
public import CORALean.ContSet.Interval.Float.Operations.BoundaryPoint
public import CORALean.ContSet.Interval.Float.Operations.Atan2Lo
public import CORALean.ContSet.Interval.Float.Operations.Atan2Hi
public import CORALean.ContSet.Interval.Float.Operations.Atan2
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Lift
public import CORALean.ContSet.Interval.Float.Operations.Dirac
public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.Interval.Float.Operations.BoundNegProj
public import CORALean.ContSet.Interval.Float.Operations.BoundProj
public import CORALean.ContSet.Interval.Float.Operations.CenterMat
public import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.DescProd
public import CORALean.ContSet.Interval.Float.Operations.MinkDiff
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.OfBounds
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds
public import CORALean.ContSet.Interval.Float.Operations.Log
public import CORALean.ContSet.Interval.Float.Operations.Sqrt
public import CORALean.ContSet.Interval.Float.Operations.Asinh
public import CORALean.ContSet.Interval.Float.Operations.Atan
public import CORALean.ContSet.Interval.Float.Operations.Asin
public import CORALean.ContSet.Interval.Float.Operations.Acos
public import CORALean.ContSet.Interval.Float.Operations.Tan
public import CORALean.ContSet.Interval.Float.Operations.Cos
public import CORALean.ContSet.Interval.Float.Operations.Sin
public import CORALean.ContSet.Interval.Float.Operations.Acosh
public import CORALean.ContSet.Interval.Float.Operations.CoshHi
public import CORALean.ContSet.Interval.Float.Operations.Kron
public import CORALean.ContSet.Interval.Float.Operations.Sign
public import CORALean.ContSet.Interval.Float.Operations.Lt
public import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.IsFullDim
public import CORALean.ContSet.Interval.Float.Operations.Isequal
public import CORALean.ContSet.Interval.Float.Operations.Transpose
public import CORALean.ContSet.Interval.Float.Operations.Ctranspose
public import CORALean.ContSet.Interval.Float.Operations.Mask
public import CORALean.ContSet.Interval.Float.Operations.Horzcat
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Sum1
public import CORALean.ContSet.Interval.Float.Operations.Volume
public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.Interval.Float.Operations.Norm
public import CORALean.ContSet.Interval.Float.Operations.CenterBox
public import CORALean.ContSet.Interval.Float.Operations.RadiusSq
public import CORALean.ContSet.Interval.Float.Operations.WidthUp
public import CORALean.ContSet.Interval.Float.Operations.Prod1
public import CORALean.ContSet.Interval.Float.Operations.Partition
public import CORALean.ContSet.Interval.Float.Operations.Enlarge
public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContSet.Interval.Float.Operations.Mrdivide
public import CORALean.ContSet.Interval.Float.Operations.QuadMap
public import CORALean.ContSet.Interval.Float.Operations.EvalList
public import CORALean.ContSet.Interval.Float.Operations.PowHi
public import CORALean.ContSet.Interval.Float.Operations.PowLo
public import CORALean.ContSet.Interval.Float.Operations.Power
public import CORALean.ContSet.Interval.Float.Operations.Magnitude
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.RoundAwayInt
public import CORALean.ContSet.Interval.Float.Operations.Round
public import CORALean.ContSet.Interval.Float.Operations.SumTermsMat
public import CORALean.ContSet.Interval.Float.Operations.Submatrix
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat

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

The same four: `max`, `min`, `isequal` and `transpose` with `ctranspose`. None rounds.

The same again: `center`, `rad`, `sum` (both axes), `volume_`, `split`, `norm_` and `radius`.
All but `split` round, and `norm_` and `radius` stop at the squared length, the root being a
certificate.
-/
