import CORALean.HybridDynamics.Definitions.Transition
import CORALean.HybridDynamics.Definitions.Location
import CORALean.HybridDynamics.Definitions.Invariant
import CORALean.HybridDynamics.Definitions.InvariantOn
import CORALean.HybridDynamics.Definitions.ReachSet
import CORALean.HybridDynamics.Definitions.RunUntil

/-!
# What a hybrid automaton means

A location is an invariant, `LinearSys` dynamics and a list of outgoing
transitions; a transition is a guard, an affine reset and a target.
`Invariant`/`InvariantOn` state that a family of sets holds it, the latter
per jump count; `ReachSet` names what a run quantifies over.
-/
