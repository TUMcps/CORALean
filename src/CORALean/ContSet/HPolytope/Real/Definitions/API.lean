import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Definitions.PolyNorm

/-!
# What a halfspace polytope means beyond its own construction

`AHPolytope` is an affine image `x̄ + X P` of one, the set `[1, Def. 2]` encodes
containment problems against without ever computing its halfspaces.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/
