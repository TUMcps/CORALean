import CORALean.Specification.Specification
import CORALean.Specification.VerifyHalfspace
import CORALean.Specification.Theorems.API
import CORALean.Specification.VerifyConvex
import CORALean.Specification.VerifyAnswer

/-!
# Specifications, collected

What a requirement is in `Specification`, and what checking one buys in
`Theorems`. Belongs to neither arithmetic layer: a specification is a set of
points, whatever computed it. `VerifyHalfspace` and `VerifyConvex` are the two
algorithms here, `[1, Alg. 2]`'s and `[1, Alg. 3]`'s decision procedures, so they
sit beside `Specification` rather than inside `Theorems`; both have their
soundness proved there.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
