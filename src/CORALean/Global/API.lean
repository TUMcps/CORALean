import CORALean.Global.Mathlib
import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.Entrywise
import CORALean.Global.Partition
import CORALean.Global.Sort
import CORALean.Global.Corners
import CORALean.Global.LinProg.API

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, the sort that chooses them, the corner combinatorics a box
needs, and the linear programming every set representation ends up asking for. Mathlib enters the project
only through this directory.

`Float/` is deliberately not collected here — it holds the floating-point
scalar, and importing it would put that in reach of every `Real` file.
-/
