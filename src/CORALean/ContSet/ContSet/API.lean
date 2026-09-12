import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.ContSet.DependencyPreserving
import CORALean.ContSet.ContSet.SupportBound
import CORALean.ContSet.ContSet.Float.SupportBound
import CORALean.ContSet.ContSet.Theorems.API

/-!
# The set interface, collected

What every representation implements: `ContSet` for what it denotes,
one class per operation — `Plus`, `LinComb`, `Reduce`, `Mtimes`, `OfPoint`,
`Recentre` — each carrying its own guarantee. `OfPoint` and `Recentre` are
independent: a representation with a centre has both, one with only a point
operation just the first.

Then two classes carrying no operation at all, `ConvexSet` and `CompactSet`:
what an algorithm has to know about a set to enclose an integral over it, asked
of the representation instead of proved again at each one.

`DependencyPreserving` carries no operation either: it is what an implementation
has when the parameters naming a subset of its operand name the corresponding
subset of its result, which is what makes a reachable subset readable at all.

`Theorems` holds what the operation classes give together: `OfPoint` and
`LinComb` already give the segment from the origin to a point.

`Float/SupportBound` is the same bound over the floating-point scalar: an
interface operation needs its bound rule here rather than in `Global`.
-/
