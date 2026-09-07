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
-/
