import CORALean.ContSet.Zonotope.Real.Definitions.Aligned
import CORALean.ContSet.Zonotope.Real.Definitions.ReduceBoxAdmissible
import CORALean.ContSet.Zonotope.Real.Definitions.OverApproxIndex
import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq
import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
import CORALean.ContSet.Zonotope.Real.Definitions.FWRadius
import CORALean.ContSet.Zonotope.Real.Definitions.FRadius
import CORALean.ContSet.Zonotope.Real.Definitions.Gradient
import CORALean.ContSet.Zonotope.Real.Definitions.GeneratorHull
import CORALean.ContSet.Zonotope.Real.Definitions.SegmentSum
import CORALean.ContSet.Zonotope.Real.Definitions.BackpropEnclose
import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet
import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
import CORALean.ContSet.Zonotope.Real.Definitions.Degree
import CORALean.ContSet.Zonotope.Real.Definitions.MinFace
import CORALean.ContSet.Zonotope.Real.Definitions.BisectInv
import CORALean.ContSet.Zonotope.Real.Definitions.WalkEdges

/-!
# What a zonotope means beyond its own construction

`Aligned` names two zonotopes whose generators point the same way, [1, Def. 3].
`ReduceBoxAdmissible` names an order whose reduction box a caller-given bound
already contains, what `reduceBoxOrder` searches for the least of.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/
