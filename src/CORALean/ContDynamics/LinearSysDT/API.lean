import CORALean.ContDynamics.LinearSysDT.BackReachExists
import CORALean.ContDynamics.LinearSysDT.BackReachForall
import CORALean.ContDynamics.LinearSysDT.BackReachSetExists
import CORALean.ContDynamics.LinearSysDT.BackReachSetForall
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.LinearSysDT.ReachSet
import CORALean.ContDynamics.LinearSysDT.Theorems.API
import CORALean.ContDynamics.LinearSysDT.Cost.API

/-!
# Discrete-time linear systems, collected

The system and what it denotes in `LinearSysDT`, reachability in `Operations`,
the set reachability encloses in `ReachSet`, the guarantees in `Theorems`, and
in `Cost` what running it costs — assembled from the operations it calls, and
the one worked composition in the tree. No `Instances`: an algorithm implements
no class.

`BackReachSetForall` is the same run read backwards — the states every
admissible input carries into a target — and `BackReachForall` computes inside
it, which is the one direction an implementation of a guarantee may claim.
`BackReachSetExists` is the other reading, where *some* input suffices, and
`BackReachExists` encloses it: a sum rather than a difference, so both halves
are outer and every representation with `Plus` and `Mtimes` runs it.
-/
