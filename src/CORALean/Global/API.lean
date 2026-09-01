import CORALean.Global.Mathlib
import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.Entrywise
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, and the sort that chooses them. Mathlib enters the project
only through this directory.

`Float/` is deliberately not collected here — it holds the floating-point
scalar, and importing it would put that in reach of every `Real` file.
-/
