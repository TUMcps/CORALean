import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# Discretizing with an exponential that can only be enclosed

`discretizeEnclosure` lands in `LinParamSysDT ℐ`, not because the system's matrix is uncertain,
`sys.A` being one fixed real matrix, but because `exp (Δt • A)` is transcendental and
`expEnclosure` is all a computation can give it. `LinParamSysDT` is where a matrix that can only be
enclosed has to live; the interval it carries is numerical error, not modelling uncertainty. The
system is the decay `ẋ = -x`, so the state moves: the run checked against `reach` is
`x(k) = (e^{-Δt})ᵏ x₀`. From there the chain is the one every `LinParamSysDT` runs: `reach`, and
`holds_of_reach` for whatever specification a caller checks the reachable set against.

## Inputs
* none

## Output
* decay system with an enclosed discretization
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet NormedSpace Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A decay, `ẋ = -x`: its flow is a contraction, and the one hypothesis the enclosure
needs is `‖Δt • A‖ / 2 = 1 / 2 < 1`. -/
def Example.sys : LinearSys ℝ 1 := LinearSys.canonical (-1)

theorem Example.hε : ‖(1:ℝ) • toRealMat Example.sys.A‖ / ((0:ℕ) + 2 : ℝ) < 1 := by
  simp [Example.sys, toRealMat]
  norm_num


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discretized system: still `LinParamSysDT`, over the interval matrix
`expEnclosure` computed for this `Δt` and this truncation order. Noncomputable: the enclosure is
built from the real matrix exponential. -/
noncomputable def Example.sysD : LinParamSysDT ℐ 1 := Example.sys.discretizeEnclosure 1 0

/-- The one matrix the enclosure is sound about: `exp (Δt • sys.A)` itself. -/
noncomputable def Example.A0 : Mat ℝ 1 1 := exp ((1:ℝ) • toRealMat Example.sys.A)

/-- The exact matrix exponential lies in the interval matrix of the discretized system. -/
theorem Example.A0_mem : Example.A0 ∈ construct Example.sysD.A :=
  MatExp.exp_mem_expEnclosure _ 0 Example.hε

/-- The initial state `1`. -/
def Example.x0 : Vec ℝ 1 := ![1]

/-- The initial set, the point `x₀`. -/
def Example.R0 : Interval (Vec ℝ 1) := Interval.point Example.x0
/-- The input set, the point `0`. -/
def Example.U : Interval (Vec ℝ 1) := Interval.point (0 : Vec ℝ 1)

/-- The run at the true exponential, `x(k) = (e^{-Δt})ᵏ x₀`: the decay itself. -/
theorem Example.traj : Example.sysD.IsCanonicalTrajectory (S := ℐ𝒱) Example.R0 Example.U
    (fun k => Example.A0 ^ k *ᵥ Example.x0) (fun _ => 0) where
  init := by rw [pow_zero, Matrix.one_mulVec]; exact Interval.mem_point _
  input _ := Interval.mem_point 0
  step k := ⟨Example.A0, Example.A0_mem, by
    simp [Matrix.mulVec_mulVec, pow_succ']⟩

/-- `reach_outer`, at the interval matrix `discretizeEnclosure` produced: the decayed
state after `k` steps is in the computed set. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.A0 ^ k *ᵥ Example.x0 ∈
      construct (Example.sysD.reach (S := ℐ𝒱) ⟨Example.R0, Example.U, 0, k⟩ ⟨o, ho⟩) :=
  Example.sysD.reach_outer (S := ℐ𝒱) ho Example.R0 Example.U Example.traj k

/-- `holds_of_reach`, closing the chain at whatever specification the caller
checks the computed reachable set against. -/
example (spec : Specification (Set (Vec ℝ 1))) {o : ℕ} (ho : 0 < o) (k : ℕ)
    (h : spec.Holds
      (construct (Example.sysD.reach (S := ℐ𝒱) ⟨Example.R0, Example.U, 0, k⟩ ⟨o, ho⟩))) :
    spec.Holds {Example.A0 ^ k *ᵥ Example.x0} :=
  Example.sysD.holds_of_reach (S := ℐ𝒱) ho Example.R0 Example.U spec Example.traj k h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
