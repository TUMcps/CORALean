module

public import CORALean.Specification.Operations.Check
public import CORALean.Specification.Operations.CheckCustomCora
public import CORALean.Specification.Operations.DiffPoint
public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Operations.VerifyConvexStep
public import CORALean.Specification.Operations.VerifyHalfspace

/-!
# Checking a specification, and the two verification decision procedures

`Check` is CORA's `check`, run through the representation pair's instances.
`VerifyHalfspace` is `[1, Alg. 2]`'s decision procedure. `VerifyConvex` is `[1, Alg. 3 (exits)]`'s,
folding `VerifyConvexStep` — each direction's test, over the witness difference `DiffPoint` —
across a fuel-bounded direction sequence. `Theorems` holds both algorithms' soundness.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
