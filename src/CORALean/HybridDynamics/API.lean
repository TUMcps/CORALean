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

The guard and the invariant do cut the reachable set, but only where an `And`
instance is available: `Theorems.JumpAndOuter` computes the guard intersection
and `Theorems.TimeIntervalInvOuter` the invariant one. A representation
without one still has `Theorems.JumpOuter`'s `hand` bargain, discharged with
nothing lost at a representation whose intersection is exact, as
`Theorems.JumpOuterConZonotope` shows.

Time-triggered only in the sense that nothing here is time-triggered: a stay
runs for a dwell time the run chooses. No parallel composition and no Zeno
analysis — the run's shape makes neither a well-formedness question, which is
the point of choosing it.

A bounded-horizon reading is `RunOn`/`InvariantOn`: the same run and invariant,
indexed by the jump count, so a location visited twice need not answer the same
set both times. `Invariant.invariantOn` reads the unbounded notion as its
constant-family special case.
-/
