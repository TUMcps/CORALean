import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn

/-!
# What `NonlinearSysDT` guarantees

That `reach` contains every trajectory, by induction on the step count — the
discrete counterpart of `NonlinearSys.relinReach_outer`, without the shifting
that continuous time forces there.
-/
