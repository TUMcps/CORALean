import CORALean.Global.Mathlib
import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.Entrywise
import CORALean.Global.Hadamard
import CORALean.Global.Partition
import CORALean.Global.Sort
import CORALean.Global.Block
import CORALean.Global.Corners
import CORALean.Global.DropIdx
import CORALean.Global.Cost
import CORALean.Global.EuclideanNorm
import CORALean.Global.Radstrom
import CORALean.Global.LinProg.API

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, the sort that chooses them, the enumeration of every index but
one, the entrywise product bundled as a bilinear map, the corner combinatorics a
box needs, the model every asserted running cost is stated against, the
Euclidean norm a vector does not carry by default, the cancellation law that
turns an outer approximation into an inner one, and the linear programming every
set representation ends up asking for. Mathlib enters the project only through
this directory.

`Float/` is deliberately not collected here — it holds the floating-point
scalar, and importing it would put that in reach of every `Real` file.
-/
