import CORALean.Specification.Operations.Check
import CORALean.Specification.Operations.DiffPoint
import CORALean.Specification.Operations.VerifyConvex
import CORALean.Specification.Operations.VerifyConvexStep
import CORALean.Specification.Operations.VerifyHalfspace

/-!
# Checking a specification, and the two verification decision procedures

`Check` is CORA's `check`, run through the representation pair's instances.
`VerifyHalfspace` is `[1, Alg. 2]`'s decision procedure. `VerifyConvex` is `[1, Alg. 3]`'s,
folding `VerifyConvexStep` — each direction's test, over the witness difference `DiffPoint` —
across a fuel-bounded direction sequence. `Theorems` holds both algorithms' soundness.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
