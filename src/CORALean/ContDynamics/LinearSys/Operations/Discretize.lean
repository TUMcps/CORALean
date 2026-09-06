import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# Sampling a continuous-time linear system

Sampling every `Δt` turns the system into the discrete-time one whose matrix is
`e^{AΔt}`, so reachability at the sample times is `LinearSysDT`'s and needs
nothing new.

The result is a `LinearSysDT ℝ`, never `LinearSysDT 𝕋`: `e^{AΔt}` is
transcendental, so no machine scalar holds it, and a float layer has to carry an
interval matrix here instead.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about this definition must make the same one — the `l∞` operator
norm — or the terms will not match.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind. -/
noncomputable def LinearSys.discretize (sys : LinearSys 𝕋 n) (Δt : ℝ) : LinearSysDT ℝ n :=
  ⟨exp (Δt • toRealMat sys.A)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
