module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Definitions.PolyNorm
public import CORALean.ContSet.HPolytope.Real.Definitions.ExtendedRow
public import CORALean.ContSet.HPolytope.Real.Definitions.NaiveHalfspaceValue

/-!
# What a halfspace polytope means beyond its own construction

`AHPolytope` is an affine image `x̄ + X P` of one, the set `[1, Def. 2]` encodes
containment problems against without ever computing its halfspaces.

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/
