import CORALean.HybridDynamics.HybridAutomaton
import CORALean.HybridDynamics.Invariant
import CORALean.HybridDynamics.InvariantOn
import CORALean.HybridDynamics.Location
import CORALean.HybridDynamics.Operations.API
import CORALean.HybridDynamics.Theorems.API
import CORALean.HybridDynamics.Transition

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

The exception is where a representation *computes* the cut: `Theorems.JumpAndOuter`
and `Theorems.TimeIntervalInvOuter` call `And.and`, homogeneous, so those two
alone ask the guard to be in `S`. Without an `And` instance there is still
`Theorems.JumpOuter`'s `hand` bargain, lossless where the intersection is
exact, as `Theorems.JumpOuterConZonotope` shows.

Time-triggered only in the sense that nothing here is: a stay runs for a dwell
time the run chooses. No parallel composition and no Zeno analysis.

A bounded-horizon reading is `RunOn`/`InvariantOn`: the same run and invariant
indexed by the jump count. `Invariant.invariantOn` is its constant-family case.
-/
