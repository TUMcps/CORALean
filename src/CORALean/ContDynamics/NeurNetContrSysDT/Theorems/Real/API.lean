import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.Real.ReachOrderLe

/-!
# What holds of `NeurNetContrSysDT` only at `𝕋 := ℝ`, collected

`ReachOrderLe` bounds `reach`'s generator count at `𝒵`, `LinearSysDT.reach_order_le`'s argument
carried across one step of the controller: `reduce_order_le` is stated at the exact zonotope, so
the scalar the network's own enclosure runs at never enters.
-/
