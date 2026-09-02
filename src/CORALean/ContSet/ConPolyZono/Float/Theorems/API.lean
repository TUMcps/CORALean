import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter

/-!
# What `ConPolyZono` guarantees

The exact layer's `plus` and `map` read as enclosures, with all five counts
unchanged.

Both rest on the constraint block surviving `toReal`: `satisfies_plus_iff` is
the exact layer's `holds_plus_iff` at the read-back matrices, and
`satisfies_mtimes` is `Iff.rfl`. Neither would be available if an operation had
rounded a constraint.
-/
