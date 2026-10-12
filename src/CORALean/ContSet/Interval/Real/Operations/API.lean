import CORALean.ContSet.Interval.Real.Operations.BoundaryRatio
import CORALean.ContSet.Interval.Real.Operations.BoundaryPoint
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Recentre
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Operations.Intersection
import CORALean.ContSet.Interval.Real.Operations.IntersectionExact
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.MinkDiff
import CORALean.ContSet.Interval.Real.Operations.LinComb
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Operations.MatMul
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Smul
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.OfBounds
import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds
import CORALean.ContSet.Interval.Real.Operations.Reindex
import CORALean.ContSet.Interval.Real.Operations.SplitAt
import CORALean.ContSet.Interval.Real.Operations.SupportBound
import CORALean.ContSet.Interval.Real.Operations.SupportBoundEntrywise
import CORALean.ContSet.Interval.Real.Operations.Uminus
import CORALean.ContSet.Interval.Real.Operations.Uplus
import CORALean.ContSet.Interval.Real.Operations.Minus
import CORALean.ContSet.Interval.Real.Operations.Infimum
import CORALean.ContSet.Interval.Real.Operations.Supremum
import CORALean.ContSet.Interval.Real.Operations.Or
import CORALean.ContSet.Interval.Real.Operations.ConvHull
import CORALean.ContSet.Interval.Real.Operations.EnclosePoints
import CORALean.ContSet.Interval.Real.Operations.Origin
import CORALean.ContSet.Interval.Real.Operations.Abs
import CORALean.ContSet.Interval.Real.Operations.Empty
import CORALean.ContSet.Interval.Real.Operations.Exp
import CORALean.ContSet.Interval.Real.Operations.Sqrt
import CORALean.ContSet.Interval.Real.Operations.Log
import CORALean.ContSet.Interval.Real.Operations.Atan
import CORALean.ContSet.Interval.Real.Operations.Sinh
import CORALean.ContSet.Interval.Real.Operations.Asinh
import CORALean.ContSet.Interval.Real.Operations.Tanh
import CORALean.ContSet.Interval.Real.Operations.Asin
import CORALean.ContSet.Interval.Real.Operations.Acos
import CORALean.ContSet.Interval.Real.Operations.Sign
import CORALean.ContSet.Interval.Real.Operations.RoundAway
import CORALean.ContSet.Interval.Real.Operations.Round
import CORALean.ContSet.Interval.Real.Operations.Le
import CORALean.ContSet.Interval.Real.Operations.Lt
import CORALean.ContSet.Interval.Real.Operations.Project
import CORALean.ContSet.Interval.Real.Operations.ProjectHighDim
import CORALean.ContSet.Interval.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.Interval.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Interval.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Interval.Real.Operations.Times
import CORALean.ContSet.Interval.Real.Operations.Norm
import CORALean.ContSet.Interval.Real.Operations.Volume
import CORALean.ContSet.Interval.Real.Operations.Max
import CORALean.ContSet.Interval.Real.Operations.Min
import CORALean.ContSet.Interval.Real.Operations.Enlarge
import CORALean.ContSet.Interval.Real.Operations.IntervalMatrix
import CORALean.ContSet.Interval.Real.Operations.Isequal
import CORALean.ContSet.Interval.Real.Operations.Radius2
import CORALean.ContSet.Interval.Real.Operations.Transpose
import CORALean.ContSet.Interval.Real.Operations.Ctranspose
import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius
import CORALean.ContSet.Interval.Real.Operations.Sum1
import CORALean.ContSet.Interval.Real.Operations.Sum2
import CORALean.ContSet.Interval.Real.Operations.Acosh
import CORALean.ContSet.Interval.Real.Operations.Atanh
import CORALean.ContSet.Interval.Real.Operations.Tan
import CORALean.ContSet.Interval.Real.Operations.Mask
import CORALean.ContSet.Interval.Real.Operations.Tril
import CORALean.ContSet.Interval.Real.Operations.Triu
import CORALean.ContSet.Interval.Real.Operations.Horzcat
import CORALean.ContSet.Interval.Real.Operations.Vertcat
import CORALean.ContSet.Interval.Real.Operations.Partition
import CORALean.ContSet.Interval.Real.Operations.Diag
import CORALean.ContSet.Interval.Real.Operations.DiagVec
import CORALean.ContSet.Interval.Real.Operations.QuadMap
import CORALean.ContSet.Interval.Real.Operations.QuadMapMixed
import CORALean.ContSet.Interval.Real.Operations.CoshLo
import CORALean.ContSet.Interval.Real.Operations.CoshHi
import CORALean.ContSet.Interval.Real.Operations.Cosh
import CORALean.ContSet.Interval.Real.Operations.MaxCos
import CORALean.ContSet.Interval.Real.Operations.Cos
import CORALean.ContSet.Interval.Real.Operations.Sin
import CORALean.ContSet.Interval.Real.Operations.Prod1
import CORALean.ContSet.Interval.Real.Operations.Kron
import CORALean.ContSet.Interval.Real.Operations.Recip
import CORALean.ContSet.Interval.Real.Operations.Rdivide
import CORALean.ContSet.Interval.Real.Operations.Mrdivide
import CORALean.ContSet.Interval.Real.Operations.Power
import CORALean.ContSet.Interval.Real.Operations.Atan2
import CORALean.ContSet.Interval.Real.Operations.EBox
import CORALean.ContSet.Interval.Real.Operations.Inf
import CORALean.ContSet.Interval.Real.Operations.Lift
import CORALean.ContSet.Interval.Real.Operations.Dirac
import CORALean.ContSet.Interval.Real.Operations.StlInterval
import CORALean.ContSet.Interval.Real.Operations.EBoxConstruct
import CORALean.ContSet.Interval.Real.Operations.SinByRegions
import CORALean.ContSet.Interval.Real.Operations.CosByRegions
import CORALean.ContSet.Interval.Real.Operations.TanByRegions
import CORALean.ContSet.Interval.Real.Operations.CotByRegions
import CORALean.ContSet.Interval.Real.Operations.ExtremalLo
import CORALean.ContSet.Interval.Real.Operations.ExtremalHi
import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseLeft
import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseRight
import CORALean.ContSet.Interval.Real.Operations.PolyBoxRevise
import CORALean.ContSet.Interval.Real.Operations.FindSolutions
import CORALean.ContSet.Interval.Real.Operations.ExploreBNVisits
import CORALean.ContSet.Interval.Real.Operations.ExploreBN
import CORALean.ContSet.Interval.Real.Operations.BoxPlaneIntersectNaive
import CORALean.ContSet.Interval.Real.Operations.BoxDiff
import CORALean.ContSet.Interval.Real.Operations.BoxDiffBounds

/-!
# What `Interval` computes

CORA's `plus`, `minkDiff`, `linComb` and `mtimes` — the last at a plain matrix and
at an interval one — one file each, plus the constructor every other
representation's `interval` goes through: a box read off `2n` certified bounds.
`minkDiff` is exact and unconditional, coordinatewise subtraction. `MatMul` is the
product of two interval matrices, not a `mtimes*` (its argument is a set of
matrices, not vectors), and `MatPow` is its plain recursive power — no lawful
`Pow` instance, since `matMul` is not associative up to equality. `Smul` scales
a box by a real, corner-swapped for a negative one. `AbsMax` is a single matrix
dominating every member of the box, for bounding its norm uniformly.

`Point` and `Center`/`Radius` are the degenerate reading of a box and the
centre-plus-deviation split the enclosure proofs elsewhere want.
`Recentre` shifts by that same centre, sound only on a nonempty box — see
`Instances.lean` for why that keeps the class itself uninstantiated.
`IsNonempty` is the predicate `Theorems/IsNonempty` characterises. `SplitAt` bisects
one coordinate at the midpoint, the splitter `NeuralNetwork.holds_of_split` is
verified at. `SupportBound` answers a direction corner by corner at `Vec ℝ n`;
`SupportBoundEntrywise` is the same over any `Entrywise` type.

Also the containment tests, `empty`, `representsa_*`, `exp`, `abs`, `times`, `project`, `max`,
`min`, `enlarge`, `radius₂`, `isequal`, `transpose`, `sum₁`, `sum₂`, `intervalMatrix`.
-/
