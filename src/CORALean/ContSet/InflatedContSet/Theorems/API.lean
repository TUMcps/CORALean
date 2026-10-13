module

public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
public import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.InflatedContSet.Theorems.IsBounded
public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

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
