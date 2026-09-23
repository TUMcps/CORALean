import CORALean.Specification.Theorems.Containment
import CORALean.Specification.Theorems.HoldsOfOuter
import CORALean.Specification.Theorems.HoldsAllOfOuter
import CORALean.Specification.Theorems.HoldsUnion
import CORALean.Specification.Theorems.HoldsIUnion
import CORALean.Specification.Theorems.Intersection
import CORALean.Specification.Theorems.InvariantOfBounds
import CORALean.Specification.Theorems.Separation
import CORALean.Specification.Theorems.SubsetHPolytope
import CORALean.Specification.Theorems.VerifyHalfspaceSafe
import CORALean.Specification.Theorems.VerifyHalfspaceUnsafe
import CORALean.Specification.Theorems.Violation
import CORALean.Specification.Theorems.VerifyConvexSafe

/-!
# Checking a specification, collected

`HoldsOfOuter` is the one that matters: it is why an outer approximation answers
a verification question at all. `HoldsUnion`/`HoldsIUnion` are the other half
of the same case split: a specification survives a union of checked sets,
which is what makes verification by splitting the input sound.
`Separation`, `Containment`, `InvariantOfBounds` and `SubsetHPolytope`
discharge the check itself, each turning it into bounds `Global.LinProg`
supplies; `Violation` and `Intersection` are the falsification exits of the
same two algorithms. `VerifyHalfspaceSafe`/`VerifyHalfspaceUnsafe` and
`VerifyConvexSafe` assemble those exits into the decision procedures'
conclusive answers.
-/
