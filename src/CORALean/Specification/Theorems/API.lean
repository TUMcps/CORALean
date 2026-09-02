import CORALean.Specification.Theorems.Containment
import CORALean.Specification.Theorems.HoldsOfOuter
import CORALean.Specification.Theorems.Separation

/-!
# Checking a specification, collected

`HoldsOfOuter` is the one that matters: it is why an outer approximation answers
a verification question at all. `Separation` and `Containment` discharge the
check itself, each turning it into bounds `Global.LinProg` supplies.
-/
