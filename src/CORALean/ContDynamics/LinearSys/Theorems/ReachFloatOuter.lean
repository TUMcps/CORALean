module

public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatTimePointOuter
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter

@[expose] public section

/-!
# `reachFloat` holds the exact flow over every window

At `t = k Δt + s`, `s ∈ [0, Δt]`, the flow is `e^{As} (e^{A k Δt} x₀)`: the inner
point is in `R_k` by `reachFloat_timePoint_outer`, and window `k` is the
run's time-interval step from `R_k`, which `timeIntervalStepFloat_outer` covers.
Nothing is asked of `η`, nor of `Δt`: the correction matrix needs it positive,
which `Reach.steps` checked before the run took a step, and `N` steps of it
span `[tStart, tFinal]` exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ} {options : LinearSys.ReachOptions 𝕋}
    {Rti Rtp : List (Zonotope (Vec 𝕋 n))} (h : sys.reachFloat params options = some (Rti, Rtp)) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rti.length = N ∧ ∀ (k : ℕ) (hk : k < Rti.length), ∀ x₀ ∈ params.X₀.construct,
        ∀ s ∈ Set.Icc 0 (toReal options.Δt),
          exp (((k : ℝ) * toReal options.Δt + s) • Scalar.toRealMat sys.A) *ᵥ x₀
            ∈ Rti[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  obtain ⟨-, -, -, htp⟩ := sys.reachFloat_timePoint_outer h
  simp only [LinearSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨N, hN, η', hη', rfl, hRtp⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  subst hRtp
  refine ⟨N, hNΔt, by simp, fun k hk x₀ hx₀ s ⟨hs0, hs⟩ => ?_⟩
  have hkp : k < N + 1 := by simp at hk; omega
  -- `e^{A (k Δt + s)} = e^{As} e^{A k Δt}`, both powers of the same matrix
  have hc : Commute (s • Scalar.toRealMat sys.A)
      (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (((k : ℝ) * toReal Δt + s) • Scalar.toRealMat sys.A) *ᵥ x₀
      = exp (s • Scalar.toRealMat sys.A)
        *ᵥ (exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    rw [← add_smul, add_comm s] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  rw [hexp, List.getElem_map, List.getElem_take]
  -- window `k` is the run's time-interval step from `R_k`, its matrices bound once
  exact sys.timeIntervalStepFloat_outer hΔt hadm _ (htp k (by simpa using hkp) x₀ hx₀) hs0 hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
