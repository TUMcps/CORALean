module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Definitions.API
public import CORALean.ContSet.ContSet.Float.API
public import CORALean.ContSet.ContSet.Operations.API
public import CORALean.ContSet.ContSet.Theorems.API
public import CORALean.ContSet.ContSet.Counterexamples.API

/-!
# The set interface, collected

What every representation implements: `ContSet` for what it denotes,
one class per operation — `Plus`, `LinComb`, `Reduce`, `Mtimes`, `OfPoint`,
`Recentre` — each carrying its own guarantee. `OfPoint` and `Recentre` are
independent: a representation with a centre has both, one with only a point
operation just the first.

`Definitions` holds two classes carrying no operation at all, `ConvexSet` and
`CompactSet` — what an algorithm has to know about a set to enclose an
integral over it, asked of the representation instead of proved again at each
one — plus `DependencyPreserving`, which is what an implementation has when
the parameters naming a subset of its operand name the corresponding subset
of its result. `Operations` holds `SupportBoundSetLinComb`, the one thing this
interface computes: a support-function bound across `Set.linComb`, CORA's
`linComb`.

`Theorems` holds what the operation classes give together: `OfPoint` and
`LinComb` already give the segment from the origin to a point.

`Float` is the same `SupportBound` rule over the floating-point scalar: an
interface operation needs its bound rule here rather than in `Global`.
-/
