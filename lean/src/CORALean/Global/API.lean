import CORALean.Global.Mathlib
import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.Entrywise
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, and the sort that chooses them. One import per file, so a
layer needs only this one. Mathlib enters the project only through this
directory.

`Float/` is the exception to a directory collecting itself here. It holds the
floating-point scalar, which only a float representation needs, and importing
it from this file would put it in reach of every `Real` file too.
-/
