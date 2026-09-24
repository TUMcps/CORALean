import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Interval.Real.Instances

/-!
# Discretizing with an exponential that can only be enclosed

`discretizeEnclosure` lands in `LinParamSysDT ℐ`, not because the system's
matrix is uncertain — `sys.A` is one fixed real matrix throughout — but because
`exp (Δt • A)` is transcendental and `expEnclosure` is all a computation can give
it. `LinParamSysDT` is simply where a matrix that can only be enclosed has to
live; the interval it carries is numerical error, not modelling uncertainty.

From there the chain is the one every `LinParamSysDT` runs: `reach`, and
`holds_of_reach` for whatever specification a caller checks the reachable set
against.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet NormedSpace Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The system left with no dynamics at all, so the one hypothesis the
enclosure needs is immediate: `‖0‖ = 0` dominates any geometric series. -/
def Example.sys : LinearSys ℝ 1 := ⟨0⟩

theorem Example.hε : ‖(1:ℝ) • toRealMat Example.sys.A‖ / ((0:ℕ) + 2 : ℝ) < 1 := by
  simp [Example.sys]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discretized system: still `LinParamSysDT`, over the interval matrix
`expEnclosure` computed for this `Δt` and this truncation order. -/
noncomputable def Example.sysD : LinParamSysDT ℐ 1 := Example.sys.discretizeEnclosure 1 0

/-- The one matrix the enclosure is sound about: `exp (Δt • sys.A)` itself. -/
noncomputable def Example.A0 : Mat ℝ 1 1 := exp ((1:ℝ) • toRealMat Example.sys.A)

theorem Example.A0_mem : Example.A0 ∈ construct Example.sysD.A :=
  MatExp.exp_mem_expEnclosure _ 0 Example.hε

def Example.x0 : Vec ℝ 1 := ![1]

def Example.R0 : Interval (Vec ℝ 1) := Interval.point Example.x0
def Example.U : Interval (Vec ℝ 1) := Interval.point (0 : Vec ℝ 1)

/-- A run at the true exponential, `exp 0 = 1`, so the state never moves. -/
theorem Example.traj : Example.sysD.Trajectory (S := ℐ𝒱) Example.R0 Example.U
    (fun _ => Example.x0) (fun _ => 0) where
  init := Interval.mem_point Example.x0
  input _ := Interval.mem_point 0
  step _ := ⟨Example.A0, Example.A0_mem, by
    simp [Example.A0, Example.sys, Example.x0, exp_zero, Matrix.one_mulVec]⟩

/-- `reach_outer`, at the interval matrix `discretizeEnclosure` produced. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.x0 ∈ construct (Example.sysD.reach (S := ℐ𝒱) o ho Example.R0 Example.U k) :=
  Example.sysD.reach_outer (S := ℐ𝒱) ho Example.R0 Example.U Example.traj k

/-- `holds_of_reach`, closing the chain at whatever specification the caller
checks the computed reachable set against. -/
example (spec : Specification (Set (Vec ℝ 1))) {o : ℕ} (ho : 0 < o) (k : ℕ)
    (h : spec.Holds (construct (Example.sysD.reach (S := ℐ𝒱) o ho Example.R0 Example.U k))) :
    spec.Holds {Example.x0} :=
  Example.sysD.holds_of_reach (S := ℐ𝒱) ho Example.R0 Example.U spec Example.traj k h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
