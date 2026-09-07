import CORALean.ContSet.Fullspace.Real.API

/-!
# The full space

CORA's `fullspace`: everything in a stated dimension, the counterpart of
`emptySet` and the unit an intersection starts from where that one is its
absorbing element.

What it denotes is unbounded at `0 < n`, which is what makes it the outer
approximation that assumes nothing — and the reason it has no `CompactSet`
instance, where `EmptySet` has one.

Real layer only: the representation holds no scalar to round.
-/
