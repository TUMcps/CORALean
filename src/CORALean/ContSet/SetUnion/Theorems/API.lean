import CORALean.ContSet.SetUnion.Theorems.MtimesExact
import CORALean.ContSet.SetUnion.Theorems.MtimesOuter
import CORALean.ContSet.SetUnion.Theorems.PlusOuter
import CORALean.ContSet.SetUnion.Theorems.ReduceOuter

/-!
# `SetUnion`'s guarantees, collected

The outer bound every operation needs for `Instances.lean`, and one theorem
beyond it: `mtimes_exact`, which `Instances.lean` does not use, since no class
here asks for equality — a caller wanting the tight guarantee for a specific
member type applies it directly, past the member's own `mtimes_outer`.
-/
