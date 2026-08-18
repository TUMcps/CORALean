import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems.PlusSubset

/-!
# What the error box guarantees

Three ways to weaken a nominal part together with its box, told apart by how the
operation moves content between the two. A representation discharges its
operations through these and never reasons about set addition itself. Building
the box is `Interval`'s business, not this class's.
-/
