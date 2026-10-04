import CORALean.ContSet.Zonotope.Real.Definitions.Aligned
import CORALean.ContSet.Zonotope.Real.Definitions.ReduceBoxAdmissible
import CORALean.ContSet.Zonotope.Real.Definitions.OverApproxIndex
import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq

/-!
# What a zonotope means beyond its own construction

`Aligned` names two zonotopes whose generators point the same way, [1, Def. 3].
`ReduceBoxAdmissible` names an order whose reduction box a caller-given bound
already contains, what `reduceBoxOrder` searches for the least of.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/
