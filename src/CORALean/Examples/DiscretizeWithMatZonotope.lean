import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotope
import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# Discretizing into a matrix zonotope, and running the same `reach`

`DiscretizeWithEnclosedExp` at `𝕄𝒵` in place of `ℐ`. The chain below is the
one that file already runs, declaration for declaration, and not one line of
`LinParamSysDT.reach`, `reach_outer` or `holds_of_reach` changes to accept it:
the recursion multiplies by `sys.A` through `Mtimes`, which never asked what
represents the matrix set.

What is gained is downstream of this file rather than visible in it. An
interval matrix bounds each entry of `e^{AΔt}` on its own, so a step forgets
that the entries move together; a matrix zonotope carries them on shared
generators, and the step is tighter for it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet NormedSpace Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The system left with no dynamics at all, so the one hypothesis the
enclosure needs is immediate: `‖0‖ = 0` dominates any geometric series. -/
def DMZ.sys : LinearSys ℝ 1 := LinearSys.canonical 0

theorem DMZ.hε : ‖(1:ℝ) • toRealMat DMZ.sys.A‖ / ((0:ℕ) + 2 : ℝ) < 1 := by
  simp [DMZ.sys]

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

/-- A run at the true exponential, `exp 0 = 1`, so the state never moves. -/
theorem DMZ.traj : DMZ.sysD.Trajectory (S := 𝒵) DMZ.R0 DMZ.U
    (fun _ => DMZ.x0) (fun _ => 0) where
  init := Zonotope.mem_ofPoint DMZ.x0
  input _ := Zonotope.mem_ofPoint 0
  step _ := ⟨DMZ.A0, DMZ.A0_mem, by
    simp [DMZ.A0, DMZ.sys, DMZ.x0, exp_zero, Matrix.one_mulVec]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach_outer`, at the matrix zonotope `discretizeMatZonotope` produced. -/
theorem DMZ.mem_reach {o : ℕ} (ho : 0 < o) (k : ℕ) :
    DMZ.x0 ∈ construct (DMZ.sysD.reach (S := 𝒵) ⟨DMZ.R0, DMZ.U, 0, k⟩ ⟨o, ho⟩) :=
  DMZ.sysD.reach_outer (S := 𝒵) ho DMZ.R0 DMZ.U DMZ.traj k

/-- `holds_of_reach`, closing the chain at whatever specification the caller
checks the computed reachable set against. -/
example (spec : Specification (Set (Vec ℝ 1))) {o : ℕ} (ho : 0 < o) (k : ℕ)
    (h : spec.Holds (construct (DMZ.sysD.reach (S := 𝒵) ⟨DMZ.R0, DMZ.U, 0, k⟩ ⟨o, ho⟩))) :
    spec.Holds {DMZ.x0} :=
  DMZ.sysD.holds_of_reach (S := 𝒵) ho DMZ.R0 DMZ.U spec DMZ.traj k h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
