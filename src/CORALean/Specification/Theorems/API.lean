module

public import CORALean.Specification.Theorems.Basic
public import CORALean.Specification.Theorems.CheckCustomCoraAnyCounterexample
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.Containment
public import CORALean.Specification.Theorems.DiffPointMemSub
public import CORALean.Specification.Theorems.ExistsConvexHullOfVerifyConvexEqUnsafe
public import CORALean.Specification.Theorems.ExistsRoundOfVerifyHalfspaceEqViolated
public import CORALean.Specification.Theorems.ExistsSeparatingOfVerifyConvexEqSafe
public import CORALean.Specification.Theorems.HoldsAllSetIntersection
public import CORALean.Specification.Theorems.HoldsCustomIff
public import CORALean.Specification.Theorems.HoldsIUnion
public import CORALean.Specification.Theorems.HoldsOfOuter
public import CORALean.Specification.Theorems.HoldsUnion
public import CORALean.Specification.Theorems.Intersection
public import CORALean.Specification.Theorems.InvariantOfBounds
public import CORALean.Specification.Theorems.Separation
public import CORALean.Specification.Theorems.SubsetHPolytope
public import CORALean.Specification.Theorems.VerifyConvexFoldInv
public import CORALean.Specification.Theorems.VerifyConvexSafe
public import CORALean.Specification.Theorems.VerifyHalfspaceSafe
public import CORALean.Specification.Theorems.VerifyHalfspaceUnsafe
public import CORALean.Specification.Theorems.Violation

/-!
# Checking a specification, collected

`HoldsOfOuter` is the one that matters: it is why an outer approximation answers
a verification question at all. `HoldsUnion`/`HoldsIUnion` are the other half
of the same case split: a specification survives a union of checked sets,
which is what makes verification by splitting the input sound.
`HoldsAllSetIntersection` reads `HoldsAll` over safe sets alone as `Holds` on
their `SetIntersection`.
`Separation`, `Containment`, `InvariantOfBounds` and `SubsetHPolytope`
discharge the check itself, each turning it into bounds `Global.LinProg`
supplies; `Violation` and `Intersection` are the falsification exits of the
same two algorithms. `VerifyHalfspaceSafe`/`VerifyHalfspaceUnsafe` and
`VerifyConvexSafe` assemble those exits into the decision procedures'
conclusive answers. `DiffPointMemSub` and `VerifyConvexFoldInv` are
`VerifyConvex`'s own loop invariant, and `ExistsSeparatingOfVerifyConvexEqSafe`/
`ExistsConvexHullOfVerifyConvexEqUnsafe` read a `safe`/`violated` verdict back
as a witness. `CheckSound` is what a passed `check` is worth.
-/
