import CORALean.Specification.Definitions.API
import CORALean.Specification.Instances
import CORALean.Specification.Operations.API
import CORALean.Specification.Specification
import CORALean.Specification.STL.API
import CORALean.Specification.Theorems.API

/-!
# Specifications, collected

What a requirement is in `Specification`, and what checking one buys in
`Theorems`. Its set is any representation, a plain `Set` among them; `Check` asks
it about a computed set through `Contains`/`IsDisjoint`, which `Instances`
computes at float boxes, zonotopes and halfspace descriptions, over any scalar.
`VerifyHalfspace` and `VerifyConvex` are the two
algorithms here, `[1, Alg. 2]`'s and `[1, Alg. 3 (exits)]`'s decision procedures — the
first in `Operations`, the second in `Definitions` beside its two soundness
theorems — and both have more soundness proved in `Theorems`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
