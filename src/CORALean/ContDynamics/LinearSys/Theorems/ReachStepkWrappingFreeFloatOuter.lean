module

public import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.SampleTimeFloatMem
public import CORALean.ContDynamics.LinearSys.Theorems.SquaringsFloatSpec

@[expose] public section

/-!
# A window of `reachWrappingFreeFloat` carries its first window by the exact `e^{A t_k}`

`t_k = k Δt` lies in its bracket `sampleTimeFloat Δt k`, so
`exp_mem_expSquaringFloat` puts `e^{A t_k}` in the window's matrix at the count
of squarings `squaringsFloat_spec` certifies, and `Mtimes.mtimes_outer` carries
every point of `R(τ_0)` through it. No sign is asked of `Δt`; `2 ≤ η` is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachStepkWrappingFreeFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η k : ℕ}
    (h2 : 2 ≤ η) {Rτ₀ : Zonotope (Vec 𝕋 n)} {y : Vec ℝ n} (hy : y ∈ Rτ₀.construct) :
    ∀ R ∈ sys.reachStepkWrappingFreeFloat Δt η Rτ₀ k,
      exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ y ∈ R.construct := by -- --- PROOF ---
  intro R (h : sys.reachStepkWrappingFreeFloat Δt η Rτ₀ k = some R)
  simp only [LinearSys.reachStepkWrappingFreeFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨sk, hsk, rfl⟩ := h
  -- `t_k` lies in its bracket
  obtain ⟨hLo, hHi⟩ := LinearSys.sampleTimeFloat_mem Δt k
  exact Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) _ Rτ₀
    (Set.mem_biUnion (sys.exp_mem_expSquaringFloat (LinearSys.squaringsFloat_spec h2 _ hsk)
      hLo hHi) (Set.mem_image_of_mem _ hy))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
