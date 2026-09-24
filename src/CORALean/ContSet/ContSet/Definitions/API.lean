import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.DependencyPreserving

/-!
# What the set interface asks of a representation, without computing anything

`ConvexSet` and `CompactSet`: what an algorithm has to know about a set to
enclose an integral over it, asked of the representation instead of proved
again at each one. `DependencyPreserving` is what an implementation has when
the parameters naming a subset of its operand name the corresponding subset
of its result.
-/
