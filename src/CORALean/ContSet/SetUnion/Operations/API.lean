module

public import CORALean.ContSet.SetUnion.Operations.Mtimes
public import CORALean.ContSet.SetUnion.Operations.Plus
public import CORALean.ContSet.SetUnion.Operations.Reduce

/-!
# `SetUnion`'s operations, collected

Every operation maps a member's own over the branches — `Mtimes` over the
whole list, `Plus` over every pair, `Reduce` over the whole list again — and
nothing here builds a new branch `S` does not already supply.
-/
