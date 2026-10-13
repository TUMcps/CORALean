module

public import CORALean.ContSet.WithEmpty.WithEmpty
public import CORALean.ContSet.WithEmpty.Instances

/-!
# A representation or nothing, collected

`WithEmpty S` is what an operation returns when its result can be empty and `S`
cannot say so — the Minkowski difference of two zonotopes is the case that
forced it. The type and what it denotes are in `WithEmpty`, the transfers of
`S`'s own classes in `Instances`.

It is not `EmptySet`, and neither replaces the other: `EmptySet n` is a
representation of its own, denoting `∅` in `n` dimensions with no `S` behind
it, where this one carries a representation *or* `∅` at whatever ambient type
`S` is written over.
-/
