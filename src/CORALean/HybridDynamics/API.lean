import CORALean.HybridDynamics.HybridAutomaton
import CORALean.HybridDynamics.Invariant
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

What the analysis needs and this directory does not supply is an intersection:
guard against reachable set, invariant against reachable set. There is no `And`
class — only two representations implement one — so every statement that would
call it takes the enclosure as a hypothesis instead, and
`Theorems.JumpOuterConZonotope` shows what it costs at a representation that
computes the intersection exactly, which is nothing.

Time-triggered only in the sense that nothing here is time-triggered: a stay
runs for a dwell time the run chooses, and a bounded-horizon analysis is the
invariant indexed by step count, which is not written. No parallel composition
and no Zeno analysis — the run's shape makes neither a well-formedness question,
which is the point of choosing it.
-/
