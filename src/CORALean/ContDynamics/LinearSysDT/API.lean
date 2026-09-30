import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachExistsOptions
import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachForallOptions
import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExists
import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForall
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Operations.API
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerFloat
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerReduced
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOrdersOptions
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinearSysDT.Instances
import CORALean.ContDynamics.LinearSysDT.Theorems.API
import CORALean.ContDynamics.LinearSysDT.Complexity.API
import CORALean.ContDynamics.LinearSysDT.Cost.API

/-!
# Discrete-time linear systems, collected

The system and what it denotes in `LinearSysDT`, reachability in `Operations`
at CORA's `options` in `ReachOptions` and its siblings, the set reachability
encloses in `ReachSet`, what a run of it owes in `ReachError` and the inner approximation
that buys in `ReachInner`, the guarantees in `Theorems`, how large the owed
error is in `Complexity`, and in `Cost` what running it costs.

`ReachUnionExact` is the set `Reach` asks to be enclosed, every step up to the
horizon, and `Instances` is the instance itself.

`ReachErrorReduced`/`ReachInnerReduced` are the same pair with the error
reduced at every step, sound since it is *added* to the exact set.
`ReachErrorFloat`/`ReachInnerFloat` are the same pair for a run computed at a
float scalar; its inner approximation sits inside the *exact* `reachSet`.

`BackReachSetForall` is the run read backwards — the states every admissible
input carries into a target — and `BackReachForall` computes inside it.
`BackReachSetExists` is the other reading, *some* input suffices, and
`BackReachExists` encloses it: a sum, so both halves are outer at `Plus,
Mtimes`. `ReachErrorOrders`/`ReachErrorReducedOrders` are `ReachError`/
`ReachErrorReduced` at `Operations.reachOrders`'s per-step order sequence.
-/
