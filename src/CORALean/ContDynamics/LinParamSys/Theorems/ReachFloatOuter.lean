import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkFloatOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepFloatOuter
import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

/-!
# `LinParamSys.reachFloat` holds every member's flow at every time of every window

`LinearSys.reachWrappingFreeFloat_outer` at a member `A ∈ sys.A`, fixed over the
whole flow: `e^{A(t_k + s)} x₀ = e^{A t_k}(e^{As} x₀)`, the inner factor in the
first window by `timeIntervalStepFloat_outer` and the outer one carried by
`reachStepkFloat_outer`. The member is the same in both, which is the
constant-parameter reading; a `ConstTrajectory` with no input is such a flow.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `mapM` into `Option` that succeeds has one result per entry, each the
function's value there. -/
theorem LinParamSys.aux_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∃ hlen : l'.length = l.length, ∀ (i : ℕ) (hi : i < l'.length),
        f (l[i]'(hlen ▸ hi)) = some l'[i] := by -- --- PROOF ---
  intro l
  induction l with
  | nil =>
    intro l' h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a l ih =>
    intro l' h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hbs
    -- the head is `f a`, the tail the induction's
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact hb
    | succ i => exact hget i (Nat.lt_of_succ_lt_succ hi)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachFloat_outer (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    {params : Reach.Params (Zonotope 𝕋 n) ℚ} {options : LinearSys.ReachOptions 𝕋}
    {Rs : List (Zonotope 𝕋 n)} (h : sys.reachFloat params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.timeStep = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ (k : ℕ) (hk : k < Rs.length), ∀ A ∈ sys.A.construct,
        ∀ x₀ ∈ params.R0.construct, ∀ s ∈ Set.Icc 0 (toReal options.timeStep),
          exp (((k : ℝ) * toReal options.timeStep + s) • A) *ᵥ x₀
            ∈ Rs[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinParamSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', hRs⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinParamSys.reachOrderFloat_spec hη').1
  obtain ⟨hlen, hget⟩ := LinParamSys.aux_mapM_some hRs
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
