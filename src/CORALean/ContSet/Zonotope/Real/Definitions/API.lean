module

public import CORALean.ContSet.Zonotope.Real.Definitions.Aligned
public import CORALean.ContSet.Zonotope.Real.Definitions.Coefficient
public import CORALean.ContSet.Zonotope.Real.Definitions.ReduceBoxAdmissible
public import CORALean.ContSet.Zonotope.Real.Definitions.OverApproxIndex
public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq
public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.ContSet.Zonotope.Real.Definitions.FWRadius
public import CORALean.ContSet.Zonotope.Real.Definitions.FRadius
public import CORALean.ContSet.Zonotope.Real.Definitions.Gradient
public import CORALean.ContSet.Zonotope.Real.Definitions.GeneratorHull
public import CORALean.ContSet.Zonotope.Real.Definitions.SegmentSum
public import CORALean.ContSet.Zonotope.Real.Definitions.BackpropEnclose
public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet
public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Definitions.Degree
public import CORALean.ContSet.Zonotope.Real.Definitions.MinFace
public import CORALean.ContSet.Zonotope.Real.Definitions.BisectInv
public import CORALean.ContSet.Zonotope.Real.Definitions.WalkEdges
public import CORALean.ContSet.Zonotope.Real.Definitions.ColsSnoc
public import CORALean.ContSet.Zonotope.Real.Definitions.MatContains

/-!
# What a zonotope means beyond its own construction

`Aligned` names two zonotopes whose generators point the same way, [1, Def. 3].
`ReduceBoxAdmissible` names an order whose reduction box a caller-given bound
already contains, what `reduceBoxOrder` searches for the least of.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/
