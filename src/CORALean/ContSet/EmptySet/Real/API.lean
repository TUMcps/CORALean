import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# The empty set, collected

The representation in `EmptySet` and the class instances in `Instances`.

Neither `Operations/` nor `Theorems/`, and both absences are the same fact:
there is one value of `EmptySet n` and one set it denotes, so every operation
on it is that value again and every guarantee about it is `∅ ⊆ _`. The
instances carry those proofs, a line each, rather than a file each.
-/
