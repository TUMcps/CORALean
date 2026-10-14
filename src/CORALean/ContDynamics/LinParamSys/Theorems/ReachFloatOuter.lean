module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkFloatOuter
public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepFloatOuter
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

@[expose] public section

/-!
# `LinParamSys.reachFloat` holds every member's flow at every time of every window

`LinearSys.reachWrappingFreeFloat_outer` at a member `A ∈ sys.A`, fixed over the
whole flow: `e^{A(t_k + s)} x₀ = e^{A t_k}(e^{As} x₀)`, the inner factor in the
first window by `timeIntervalStepFloat_outer` and the outer one carried by
`reachStepkFloat_outer`. The member is the same in both, which is the
constant-parameter reading; a `ConstTrajectory` with no input is such a flow.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachFloat_outer (sys : LinParamSys ℐ[𝕋] n)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ} {options : LinearSys.ReachOptions 𝕋}
    {Rs : List (Zonotope (Vec 𝕋 n))} (h : sys.reachFloat params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ (k : ℕ) (hk : k < Rs.length), ∀ A ∈ sys.A.construct,
        ∀ x₀ ∈ params.X₀.construct, ∀ s ∈ Set.Icc 0 (toReal options.Δt),
          exp (((k : ℝ) * toReal options.Δt + s) • A) *ᵥ x₀
            ∈ Rs[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinParamSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', hRs⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinParamSys.reachOrderFloat_spec hη').1
  obtain ⟨hlen, hget⟩ := LinParamSys.mapM_eq_some hRs
  rw [List.length_range] at hlen
  refine ⟨N, hNΔt, hlen, fun k hk A hA x₀ hx₀ s ⟨hs0, hs⟩ => ?_⟩
  -- `e^{As} x₀` is in the first window, reduced or not
  have hτ₀ := Reduce.reduce_outer (sys.timeIntervalStepFloat Δt η' X₀) ρ
    (sys.timeIntervalStepFloat_outer hΔt hadm X₀ hA hx₀ hs0 hs)
  have hwin := hget k hk
  simp only [List.getElem_range] at hwin
  -- `e^{A (t_k + s)} = e^{A t_k} e^{As}`, both powers of the same member
  have hc : Commute (((k : ℝ) * toReal Δt) • A) (s • A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (((k : ℝ) * toReal Δt + s) • A) *ᵥ x₀
      = exp (((k : ℝ) * toReal Δt) • A) *ᵥ (exp (s • A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    rw [← add_smul] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  rw [hexp]
  exact sys.reachStepkFloat_outer hadm.1 hwin hA hτ₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
