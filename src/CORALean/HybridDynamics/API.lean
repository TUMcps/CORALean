module

public import CORALean.HybridDynamics.HybridAutomaton
public import CORALean.HybridDynamics.Definitions.API
public import CORALean.HybridDynamics.Operations.API
public import CORALean.HybridDynamics.Theorems.API
public import CORALean.HybridDynamics.Counterexamples.API
public import CORALean.HybridDynamics.Complexity.API
public import CORALean.HybridDynamics.Parallel.API
public import CORALean.HybridDynamics.TimeTriggered.API

/-!
# Hybrid automata, collected

CORA's `hybridDynamics`. A location is an invariant, `LinearSys` dynamics and a
list of outgoing transitions; a transition is a guard, an affine reset and a
target; and a run alternates the two, written as an inductive family so that
chaining a guarantee along it is the family's own recursion.

The guard and the invariant carry their own representation `G`, apart from the
state's `S`, and every statement here asks `ContSet` of it and nothing else:
they are read as `construct e.guard` and `construct ℓ.inv`, never computed with
(#39). `Examples.BouncingBall` is a zonotope state with halfspace guards.

The exception is where a representation *computes* the cut: `Theorems.JumpIntersectionOuter`
and `Theorems.TimeIntervalInvOuter` call `Intersection.intersection`, homogeneous, so those two
alone ask the guard to be in `S`. Without one there is still `Theorems.JumpOuter`'s
`hinter` bargain, lossless where exact, as `Theorems.JumpOuterConZonotope` shows.

Time-triggered only in the sense that nothing here is: a stay runs for a dwell
time the run chooses, and a bounded-horizon reading is `RunOn`/`InvariantOn`,
the same run and invariant indexed by the jump count — `Invariant.invariantOn`
its constant-family case. `ReachSet` names what `Run` quantifies over: `reachSet`
at a location, `reachLocations` over all, [1, Def. 3.4]'s two reachable sets.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
