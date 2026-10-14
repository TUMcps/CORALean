module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# Sampling a continuous-time linear system

Sampling every `Δt` turns the system's canonical form into the discrete-time one whose matrix
is `e^{AΔt}`, `LinearSysDT.canonical`, its input what a step accumulates in state coordinates,
so reachability at the sample times is `LinearSysDT`'s and needs nothing new.

The result is a `LinearSysDT ℝ`, never `LinearSysDT 𝕋`: `e^{AΔt}` is
transcendental, so no machine scalar holds it, and a float layer has to carry an
interval matrix here instead.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about this definition must make the same one — the `l∞` operator
norm — or the terms will not match.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind. -/
noncomputable def LinearSys.discretize (sys : LinearSys 𝕋 n) (Δt : ℝ) : LinearSysDT ℝ n :=
  LinearSysDT.canonical (exp (Δt • toRealMat sys.A))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
