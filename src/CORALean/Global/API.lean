import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.ExactScalar
import CORALean.Global.NegScalar
import CORALean.Global.Entrywise
import CORALean.Global.Hadamard
import CORALean.Global.Partition
import CORALean.Global.Sort
import CORALean.Global.Block
import CORALean.Global.BlockDiag
import CORALean.Global.AppendProdAdd
import CORALean.Global.AppendLinear
import CORALean.Global.Corners
import CORALean.Global.DropIdx
import CORALean.Global.FoldInduction
import CORALean.Global.CrossProduct
import CORALean.Global.Cost
import CORALean.Global.BoxDiameter
import CORALean.Global.BoxDiameterAddLe
import CORALean.Global.BoxDiameterMulVecImageLe
import CORALean.Global.Err
import CORALean.Global.EuclideanNorm
import CORALean.Global.EuclideanHausdorffDist
import CORALean.Global.EuclideanHausdorffDistAddLe
import CORALean.Global.EuclideanHausdorffDistTriangle
import CORALean.Global.EuclideanHausdorffDistZero
import CORALean.Global.EuclideanGenOpNorm
import CORALean.Global.Radstrom
import CORALean.Global.RadstromEq
import CORALean.Global.RadstromHausdorff
import CORALean.Global.Caratheodory
import CORALean.Global.ConeEdge
import CORALean.Global.EqSmulNCross
import CORALean.Global.Minimax
import CORALean.Global.SuperlinearDecrease
import CORALean.Global.ErrorConvergesToZero
import CORALean.Global.HorizonErrorBudget
import CORALean.Global.ConvergenceOrder
import CORALean.Global.LinProg.API
import CORALean.Global.TaylorRemainder
import CORALean.Global.CoeffDomination
import CORALean.Global.ElementaryDerivBounds

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, the sort that chooses them, the enumeration of every index but
one, the induction principle carrying a property through a `Fin.foldl`, the
`n`-dimensional cross product that enumeration builds, the entrywise
product bundled as a bilinear map, the corner combinatorics a
box needs, the model every asserted running cost is stated against, the width of
the tightest box over a set and the origin-centred Euclidean radius of that box
(`err`), the Euclidean norm a vector does not carry by default, the Hausdorff
distance read through it, a family of generators' own induced operator norm
(`genOpNorm₂`), the cancellation law that
turns an outer approximation into an inner one, Carathéodory's theorem over a
fixed index, the minimax inequality a parametrized infimum's continuity gives
over two compact sets, when a set-based evaluation shrinks superlinearly, when a
step error converges to zero, a fixed horizon's error budget, the classical
convergence order a point-valued ODE solver either has or does not, and the
linear programming every set representation ends up asking for.

`Float/` is deliberately not collected here — it holds the floating-point
scalar, and importing it would put that in reach of every `Real` file.
-/
