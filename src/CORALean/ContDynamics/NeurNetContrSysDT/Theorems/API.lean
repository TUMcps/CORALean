import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryIterate

/-!
# What a network in the loop guarantees

`ReachOuter` is the composition of the two halves, `HoldsOfReach` what checking
a specification on it buys, and `TrajectoryIterate` the reading of a run that a
determined input forces: an orbit, not a family.
-/
