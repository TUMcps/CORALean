import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsMulVec
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectory
import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
import CORALean.HybridDynamics.Parallel.Theorems.RunMemOfInvariant
import CORALean.HybridDynamics.Parallel.Theorems.ReachSetSubsetInvariant

/-!
# What a parallel hybrid automaton guarantees, collected

`MergeFlowsMulVec` and `LiftTransitionReset` are the two identities the product's flow and
jump are read through; `StayTrajectory` takes a shared stay to a stay of the product and
`RunToProduct` a run to a run, by induction. `RunMemOfInvariant` and `ReachSetSubsetInvariant`
are the single automaton's outer-approximation theorems, stated against the parallel one.
-/
