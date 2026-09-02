import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

/-!
# What `LinearSysDT` guarantees

That `reach` contains every trajectory, which is the one thing there is to
prove about a discrete run, and what checking a specification on it then buys.
`ReachOneOuter` is its step in isolation, which is what a run whose input set
changes each step — a closed loop — takes instead.
-/
