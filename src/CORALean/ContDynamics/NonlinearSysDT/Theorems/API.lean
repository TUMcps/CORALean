import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateTrajectory

/-!
# What `NonlinearSysDT` guarantees

That `reach` contains every trajectory, by induction on the step count — the
discrete counterpart of `NonlinearSys.relinReach_outer`, without the shifting
that continuous time forces there.

`SimulateTrajectory`/`SimulateMemReach` are `simulate` sampling one run and
landing inside `reach`, at whatever confinement `reach_outer` itself needs per
step — no falsification corollary here, since this class has no
`holds_of_reach` to contrapose: confinement is a hypothesis checked afterwards,
not a certificate a specification check could stand in for.
-/
