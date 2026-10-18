module

public import CORALean.ContSet.SetIntersection.Operations.Intersection
public import CORALean.ContSet.SetIntersection.Operations.Mtimes
public import CORALean.ContSet.SetIntersection.Operations.Plus
public import CORALean.ContSet.SetIntersection.Operations.Reduce

/-!
# `SetIntersection`'s operations, collected

Every operation maps a member's own over the branches, the same shape
`SetUnion`'s operations use: `Mtimes` over the whole list, `Plus` over every
pair, `Reduce` over the whole list again; `Intersection` appends two lists.
-/
