import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotope
import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# Discretizing into a matrix zonotope, and running the same `reach`

`DiscretizeWithEnclosedExp` at `𝕄𝒵` in place of `ℐ`. The chain is the one that file already runs,
declaration for declaration, and not one line of `LinParamSysDT.reach`, `reach_outer` or
`holds_of_reach` changes to accept it: the recursion multiplies by `sys.A` through `Mtimes`, which
never asked what represents the matrix set. The system is the decay `ẋ = -x`, so the run checked
against `reach` is `x(k) = (e^{-Δt})ᵏ x₀`. What is gained is downstream: an interval matrix bounds
each entry of `e^{AΔt}` on its own, so a step forgets that the entries move together; a matrix
zonotope carries them on shared generators, and the step is tighter for it.

## Inputs
* `o` – zonotope order
* `k` – step count

## Hypotheses
* `ho` – zonotope order positive

## Conclusion
* the exact state lies in the reach set
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
def DMZ.sys : LinearSys ℝ 1 := LinearSys.canonical (-1)

theorem DMZ.hε : ‖(1:ℝ) • toRealMat DMZ.sys.A‖ / ((0:ℕ) + 2 : ℝ) < 1 := by
  simp [DMZ.sys, toRealMat]
  norm_num

/-- The discretized system, over the matrix zonotope `expMatZonoEnclosure`
computed for this `Δt` and this truncation order. -/
noncomputable def DMZ.sysD : LinParamSysDT 𝕄𝒵 1 := DMZ.sys.discretizeMatZonotope 1 0

/-- The one matrix the enclosure is sound about: `exp (Δt • sys.A)` itself. -/
noncomputable def DMZ.A0 : Mat ℝ 1 1 := exp ((1:ℝ) • toRealMat DMZ.sys.A)

/-- `hε` is checked at `‖Δt • A‖`; `norm_absMax_ofPoint` carries it to the
dominating matrix `expMatZonoEnclosure` states it at. -/
theorem DMZ.A0_mem : DMZ.A0 ∈ construct DMZ.sysD.A :=
  MatExp.exp_mem_expMatZonoEnclosure _ 0 (Zonotope.mem_ofPoint _)
    (by rw [Zonotope.norm_absMax_ofPoint]; exact DMZ.hε)

def DMZ.x0 : Vec ℝ 1 := ![1]

noncomputable def DMZ.R0 : Zonotope (Vec ℝ 1) := Zonotope.ofPoint DMZ.x0
noncomputable def DMZ.U : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (0 : Vec ℝ 1)

/-- The run at the true exponential, `x(k) = (e^{-Δt})ᵏ x₀`: the decay itself. -/
theorem DMZ.traj : DMZ.sysD.IsCanonicalTrajectory (S := 𝒵) DMZ.R0 DMZ.U
    (fun k => DMZ.A0 ^ k *ᵥ DMZ.x0) (fun _ => 0) where
  init := by rw [pow_zero, Matrix.one_mulVec]; exact Zonotope.mem_ofPoint _
  input _ := Zonotope.mem_ofPoint 0
  step k := ⟨DMZ.A0, DMZ.A0_mem, by
    simp [Matrix.mulVec_mulVec, pow_succ']⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach_outer`, at the matrix zonotope `discretizeMatZonotope` produced. -/
theorem DMZ.mem_reach {o : ℕ} (ho : 0 < o) (k : ℕ) :
    DMZ.A0 ^ k *ᵥ DMZ.x0 ∈ construct (DMZ.sysD.reach (S := 𝒵) ⟨DMZ.R0, DMZ.U, 0, k⟩ ⟨o, ho⟩) :=
  DMZ.sysD.reach_outer (S := 𝒵) ho DMZ.R0 DMZ.U DMZ.traj k

/-- `holds_of_reach`, closing the chain at whatever specification the caller
checks the computed reachable set against. -/
example (spec : Specification (Set (Vec ℝ 1))) {o : ℕ} (ho : 0 < o) (k : ℕ)
    (h : spec.Holds (construct (DMZ.sysD.reach (S := 𝒵) ⟨DMZ.R0, DMZ.U, 0, k⟩ ⟨o, ho⟩))) :
    spec.Holds {DMZ.A0 ^ k *ᵥ DMZ.x0} :=
  DMZ.sysD.holds_of_reach (S := 𝒵) ho DMZ.R0 DMZ.U spec DMZ.traj k h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
