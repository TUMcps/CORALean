import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
import CORALean.ContSet.InflatedContSet.Theorems.Convex
import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
import CORALean.ContSet.InflatedContSet.Theorems.IsBounded
import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

/-!
# What the error box guarantees

Four ways to weaken a nominal part together with its box, told apart by how the
operation moves content between the two. A representation discharges its
operations through these and never reasons about set addition itself.

And what the box leaves alone: a nominal part that is convex, compact or bounded
stays so with its box added (`convex_construct`, `isCompact_construct`,
`isBounded_construct`), whatever the nominal representation; and a linear image
distributes over the sum (`image_add`).
-/
