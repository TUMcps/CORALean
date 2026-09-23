import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExists
import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForall
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Operations.API
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerFloat
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerReduced
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
import CORALean.ContDynamics.LinearSysDT.Theorems.API
import CORALean.ContDynamics.LinearSysDT.Complexity.API
import CORALean.ContDynamics.LinearSysDT.Cost.API

/-!
# Discrete-time linear systems, collected

The system and what it denotes in `LinearSysDT`, reachability in `Operations`,
the set reachability encloses in `ReachSet`, what a run of it owes in
`ReachError` and the inner approximation that buys in `ReachInner`, the
guarantees in `Theorems`, how large the owed error is in `Complexity`, and in
`Cost` what running it costs. No `Instances`: an algorithm implements no class.

`ReachErrorReduced` and `ReachInnerReduced` are the same pair with the error
reduced at every step, sound because the error is *added* to the exact set.
`ReachErrorFloat` and `ReachInnerFloat` are the same pair for a run computed at
a float scalar, where every operation loses ground, not only `reduce`; its
inner approximation sits inside the *exact*, real-valued `reachSet`.

`BackReachSetForall` is the same run read backwards — the states every
admissible input carries into a target — and `BackReachForall` computes inside
it, which is the one direction an implementation of a guarantee may claim.
`BackReachSetExists` is the other reading, where *some* input suffices, and
`BackReachExists` encloses it: a sum rather than a difference, so both halves
are outer and every representation with `Plus` and `Mtimes` runs it.

`ReachErrorOrders` and `ReachErrorReducedOrders` are `ReachError` and
`ReachErrorReduced` at `Operations.reachOrders`'s per-step order sequence.
-/
