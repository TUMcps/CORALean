import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.ContSet.SupportBound

/-!
# The set interface, collected

What every representation implements: `ContSet` for what it denotes,
one class per operation — `Plus`, `LinComb`, `Reduce`, `Mtimes` — each carrying
its own guarantee.

Then two classes carrying no operation at all, `ConvexSet` and `CompactSet`:
what an algorithm has to know about a set to enclose an integral over it, asked
of the representation instead of proved again at each one.
-/
