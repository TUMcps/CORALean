import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.DependencyPreserving
import CORALean.ContSet.ContSet.Definitions.FullDimTest
import CORALean.ContSet.ContSet.Definitions.IsFullDim
import CORALean.ContSet.ContSet.Definitions.SupportFunc
import CORALean.ContSet.ContSet.Definitions.DimReduce
import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
import CORALean.ContSet.ContSet.Definitions.IsBoundIntersect2D
import CORALean.ContSet.ContSet.Definitions.ExactVertices

/-!
# What the set interface asks of a representation, without computing anything

`ConvexSet` and `CompactSet`: what an algorithm has to know about a set to
enclose an integral over it, asked of the representation instead of proved
again at each one. `DependencyPreserving` is what an implementation has when
the parameters naming a subset of its operand name the corresponding subset
of its result. `FullDimTest` is `isFullDim` as a conservative test.
-/
