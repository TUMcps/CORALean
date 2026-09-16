import CORALean.Specification.Specification
import CORALean.Specification.VerifyHalfspace
import CORALean.Specification.Theorems.API

/-!
# Specifications, collected

What a requirement is in `Specification`, and what checking one buys in
`Theorems`. Belongs to neither arithmetic layer: a specification is a set of
points, whatever computed it. `VerifyHalfspace` is the one algorithm here,
`[1, Alg. 2]`'s decision procedure, its soundness proved in `Theorems`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
