import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsMulVec
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectory
import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
import CORALean.HybridDynamics.Parallel.Theorems.RunMemOfInvariant
import CORALean.HybridDynamics.Parallel.Theorems.ReachSetSubsetInvariant
import CORALean.HybridDynamics.Parallel.Theorems.UnstackStack
import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
import CORALean.HybridDynamics.Parallel.Theorems.StackApply
import CORALean.HybridDynamics.Parallel.Theorems.BlockProjApply
import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdA
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdb
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdAe
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdbe
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeComapBlockProjExact
import CORALean.HybridDynamics.Parallel.Theorems.BoxLifting

/-!
# What a parallel hybrid automaton guarantees, collected

`MergeFlowsMulVec` and `LiftTransitionReset` are the two identities the product's flow and
jump are read through; `StayTrajectory` takes a shared stay to a stay of the product and
`RunToProduct` a run to a run, by induction. `RunMemOfInvariant` and `ReachSetSubsetInvariant`
are the single automaton's outer-approximation theorems, stated against the parallel one.
`StackUnstack` and its neighbours relate `stack` to `unstack`; `IntervalStackProdExact` and
`HPolytopeStackProdExact` say the two Cartesian products are exact, `HPolytopeComapBlockProjExact`
the guard's lift. `BoxLifting` is the first concrete `Lifting`: boxes for inputs and halfspace
descriptions for invariants and guards.
-/
