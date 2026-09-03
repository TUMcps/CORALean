import CORALean.ContSet.ConPolyZono.Float.Theorems.AndOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter

/-!
# What `ConPolyZono` guarantees

The exact layer's `plus`, `map` and `and` read as enclosures, `dependent` still
exactly, and all five counts unchanged throughout.

`plus` and `mtimes` rest on the constraint block surviving `toReal`:
`satisfies_plus_iff` is the exact layer's `holds_plus_iff` at the read-back
matrices, and `satisfies_mtimes` is `Iff.rfl`.

`and_outer` is the one that computes a constraint, and it is the file to read.
The two nominal points it has to make agree differ by whatever the two error
boxes admit, so the agreement rows carry an interval wide enough for that
difference — which leaves the rounding of the centres nowhere to go but into an
interval that was going to be widened anyway.
-/
