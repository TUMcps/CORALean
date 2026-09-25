import CORALean.ContDynamics.LinearSys.Operations.ReachStepkFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Theorems.WindowOrderFloatSpec

/-!
# A window of `reachFloat` carries its first window by the exact `e^{A t_k}`

`t_k = k Δt` lies between `nsmulDown k Δt` and `nsmulUp k Δt`, so
`exp_mem_expIntervalFloat` puts `e^{A t_k}` in the window's matrix at the order
`windowOrderFloat_spec` certifies, and `Mtimes.mtimes_outer` carries every point
of `R(τ_0)` through it. No sign is asked of `Δt`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachStepkFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η k : ℕ}
    {Rτ₀ R : Zonotope 𝕋 n} (h : sys.reachStepkFloat Δt η Rτ₀ k = some R) {y : Vec ℝ n}
    (hy : y ∈ Rτ₀.construct) :
    exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ y ∈ R.construct := by -- --- PROOF ---
  simp only [LinearSys.reachStepkFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨ηk, hηk, rfl⟩ := h
  -- `t_k` lies between its two rounded sums
  have hLo := nsmulDown_le k Δt
  have hHi := le_nsmulUp k Δt
  exact Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) _ Rτ₀
    (Set.mem_biUnion (sys.exp_mem_expIntervalFloat (LinearSys.windowOrderFloat_spec hηk).1
      hLo hHi) (Set.mem_image_of_mem _ hy))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
