module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Definitions.DependencyPreserving
public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import CORALean.ContSet.ContSet.Definitions.SupportFunc
public import CORALean.ContSet.ContSet.Definitions.DimReduce
public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import CORALean.ContSet.ContSet.Definitions.IsBoundIntersect2D

/-!
# What the set interface asks of a representation, without computing anything

`ConvexSet` and `CompactSet`: what an algorithm has to know about a set to
enclose an integral over it, asked of the representation instead of proved
again at each one. `DependencyPreserving` is what an implementation has when
the parameters naming a subset of its operand name the corresponding subset
of its result. `FullDimTest` is `isFullDim` as a conservative test.
-/
