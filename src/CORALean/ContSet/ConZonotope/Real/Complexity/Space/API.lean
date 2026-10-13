module

public import CORALean.ContSet.ConZonotope.Real.Complexity.Space.Intersection
public import CORALean.ContSet.ConZonotope.Real.Complexity.Space.Plus
public import CORALean.ContSet.ConZonotope.Real.Complexity.Space.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Complexity.Space.LinComb
public import CORALean.ContSet.ConZonotope.Real.Complexity.Space.Reduce

/-!
# What `ConZonotope` costs

The size of an operation's result as a function of its operands' — the
generator count `h` a zonotope already has, plus the inequality and equality
counts `P.m` and `P.me` this representation adds. Each equality is `rfl`
against the structure instance in `Operations/`, `P.me` after unfolding one
`0 + ·` the unit box's own equality count leaves behind.

`reduce`'s bound is on `P.m` and `P.me` only, and unconditional: neither count
can grow, since `reduce` either passes `C` through or drops every constraint
to `fullspace`'s zero. No bound on `h` is stated — `Reduce.lean`'s docstring
says why.

The number of scalar operations each operation costs is not yet stated here.
-/
