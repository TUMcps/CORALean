import CORALean.Global.Mathlib
import CORALean.Global.Tensor
import CORALean.Global.Partition
import CORALean.Global.ContSet

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, index partitions, and the
`ContSet` interface they each instantiate. One import per file, so a layer needs
only this one. Mathlib enters the project only through this directory.
-/
