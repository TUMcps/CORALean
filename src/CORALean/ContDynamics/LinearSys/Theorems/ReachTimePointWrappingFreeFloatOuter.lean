module

public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
public import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointWrappingFreeFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkWrappingFreeFloatOuter

@[expose] public section

/-!
# `reachTimePointWrappingFreeFloat` holds the exact flow at every sample time

At `t_k = k Δt`, the flow is `e^{A t_k} x₀`: `reachStepkWrappingFreeFloat_outer` carries
every point of `X₀` through the window's matrix directly, `k = 0` included --
`e^{A · 0} = I` needs nothing beyond that same lemma. `η'` is the order the
run used, certified admissible by `reachOrderFloat_spec` exactly as
`reachWrappingFreeFloat_outer` uses it, `N` spanning `[tStart, tFinal]` as there;
`LinParamSys.mapM_eq_some` reads one `mapM` result per `k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachTimePointWrappingFreeFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- STMT ---
    ∀ Rs ∈ sys.reachTimePointWrappingFreeFloat params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N + 1 ∧ ∀ (k : ℕ) (hk : k < Rs.length), ∀ x₀ ∈ params.X₀.construct,
          exp (((k : ℝ) * toReal options.Δt) • Scalar.toRealMat sys.A) *ᵥ x₀
            ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (h : sys.reachTimePointWrappingFreeFloat params options = some Rs)
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.reachTimePointWrappingFreeFloat, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', hRs⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  obtain ⟨hlen, hget⟩ := LinParamSys.mapM_eq_some hRs
  rw [List.length_range] at hlen
  refine ⟨N, (Reach.steps_spec_toReal _ hN).2, hlen, fun k hk x₀ hx₀ => ?_⟩
  have hwin := hget k hk
  simp only [List.getElem_range] at hwin
  -- window `k` is `reachStepkWrappingFreeFloat` at `X₀` directly, `k = 0` included
  exact sys.reachStepkWrappingFreeFloat_outer hadm.1 hx₀ _ hwin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
