module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.SetIntersection.Theorems.MtimesOuter
public import CORALean.ContSet.SetIntersection.Theorems.PlusOuter
public import CORALean.ContSet.SetIntersection.Theorems.ReduceOuter

/-!
# `SetIntersection`'s guarantees, collected

Outer only, unlike `SetUnion`: every guarantee here reads `⊆` in the direction
an intersection shrinks, and even a member type whose own operation is exact
gains nothing further at the intersection, since combining branches after
mapping is what throws the equality away.
-/
