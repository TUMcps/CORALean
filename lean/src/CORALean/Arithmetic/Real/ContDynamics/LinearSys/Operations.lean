import CORALean.Arithmetic.Real.ContDynamics.LinearSys.LinearSys
import CORALean.Arithmetic.Real.ContDynamics.LinearSysDT.API

/-!
# Continuous-time linear systems: sampling

Sampling every `Δt` turns the system into the discrete-time one whose matrix is
`e^{AΔt}`, so reachability at the sample times is `LinearSysDT`'s and needs
nothing new. What the inputs contribute over a step is `stepInput`, an integral
rather than a set: enclosing it is the representation's job, not this file's.

The result is a `LinearSysDT ℝ`, never `LinearSysDT 𝕋`: `e^{AΔt}` is
transcendental, so no machine scalar holds it. A float layer has to carry an
interval matrix here instead.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these definitions must make the same one — the `l∞`
operator norm — or the terms will not match.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

/-- The system a step of `Δt` leaves behind. -/
noncomputable def LinearSys.discretize (sys : LinearSys 𝕋 n) (Δt : ℝ) : LinearSysDT ℝ n :=
  ⟨exp (Δt • toRealMat sys.A)⟩

/-- Everything the input contributed over step `k`, propagated to its end. -/
noncomputable def LinearSys.stepInput (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ)
    (k : ℕ) : Vec ℝ n :=
  ∫ s in (k * Δt)..((k + 1) * Δt), exp (((k + 1) * Δt - s) • toRealMat sys.A) *ᵥ u s

end CORALean.Arithmetic.Real
