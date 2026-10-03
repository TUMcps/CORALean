import CORALean.HybridDynamics.Definitions.Transition
import CORALean.HybridDynamics.Definitions.Location
import CORALean.HybridDynamics.Definitions.Invariant
import CORALean.HybridDynamics.Definitions.InvariantOn
import CORALean.HybridDynamics.Definitions.ReachSet
import CORALean.HybridDynamics.Definitions.RunUntil
import CORALean.HybridDynamics.Definitions.NonlinearReset
import CORALean.HybridDynamics.Definitions.ConstFlowHitSet
import CORALean.HybridDynamics.Definitions.HitSet
import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.HybridDynamics.Definitions.HitHessian
import CORALean.HybridDynamics.Definitions.HitJacobian
import CORALean.HybridDynamics.Definitions.HitPoint

/-!
# What a hybrid automaton means

A location is an invariant, `LinearSys` dynamics and a list of outgoing
transitions; a transition is a guard, an affine reset and a target.
`Invariant`/`InvariantOn` state that a family of sets holds it, the latter
per jump count; `ReachSet` names what a run quantifies over.
-/
