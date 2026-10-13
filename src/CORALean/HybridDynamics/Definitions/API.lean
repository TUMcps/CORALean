module

public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.HybridDynamics.Definitions.Invariant
public import CORALean.HybridDynamics.Definitions.InvariantOn
public import CORALean.HybridDynamics.Definitions.ReachSet
public import CORALean.HybridDynamics.Definitions.RunUntil
public import CORALean.HybridDynamics.Definitions.UrgentRun
public import CORALean.HybridDynamics.Definitions.UrgentReachSetAt
public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel
public import CORALean.HybridDynamics.Definitions.NonlinHybridAutomaton
public import CORALean.HybridDynamics.Definitions.ConstFlowHitSet
public import CORALean.HybridDynamics.Definitions.CheckFlow
public import CORALean.HybridDynamics.Definitions.CheckFlowCora
public import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirard
public import CORALean.HybridDynamics.Definitions.RobustProjectionCora
public import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirardCora
public import CORALean.HybridDynamics.Definitions.HitSet
public import CORALean.HybridDynamics.Definitions.SdcInput
public import CORALean.HybridDynamics.Definitions.HitHessian
public import CORALean.HybridDynamics.Definitions.HitHessianNum
public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Definitions.ResetTaylor
public import CORALean.HybridDynamics.Definitions.IdentHA
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.HybridDynamics.Definitions.HitEnclosure

/-!
# What a hybrid automaton means

A location is an invariant, `LinearSys` dynamics and a list of outgoing
transitions; a transition is a guard, an affine reset and a target.
`Invariant`/`InvariantOn` state that a family of sets holds it, the latter
per jump count; `ReachSet` names what a run quantifies over.
-/
