module

public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepFloatOuter

@[expose] public section

/-!
# `reachFloat`'s time-point sets hold the exact flow at `k Δt`

By induction on `k`: `R_0 = X₀` holds `e^{0} x₀ = x₀`, and
`e^{A (k+1) Δt} x₀ = e^{AΔt} (e^{A k Δt} x₀)`, which `timePointStepFloat_outer`
puts in `[e^{AΔt}] R_k` — the run's step, its matrix computed once — and
`Reduce.reduce_outer` keeps in `R_{k+1}`. The run's `N` is the one `Reach.steps`
derived, so `N` time steps span `[tStart, tFinal]` exactly (`steps_spec_toReal`).

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – reach options

## Hypotheses
* none

## Conclusion
* the exact flow from every initial point lies in the time-point sets
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

theorem LinearSys.reachFloat_timePoint_outer (sys : LinearSys 𝕋 n)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rti Rtp, (Rti, Rtp) ∈ sys.reachFloat params options →
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rtp.length = N + 1 ∧ ∀ (k : ℕ) (hk : k < Rtp.length), ∀ x₀ ∈ params.X₀.construct,
          exp (((k : ℝ) * toReal options.Δt) • Scalar.toRealMat sys.A) *ᵥ x₀
            ∈ Rtp[k].construct := by -- --- PROOF ---
  intro Rti Rtp (h : sys.reachFloat params options = some (Rti, Rtp))
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨N, hN, η', hη', -, rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  refine ⟨N, (Reach.steps_spec_toReal _ hN).2, List.length_iterate _ _ _, fun k hk x₀ hx₀ => ?_⟩
  rw [List.getElem_iterate]
  clear hk
  induction k with
  | zero => simp [hx₀]
  | succ k ih =>
    -- `e^{A (k+1) Δt} = e^{AΔt} e^{A k Δt}`, both powers of the same matrix
    have hc : Commute (toReal Δt • Scalar.toRealMat sys.A)
        (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have hexp : exp ((((k + 1 : ℕ) : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ x₀
        = exp (toReal Δt • Scalar.toRealMat sys.A)
          *ᵥ (exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ x₀) := by
      have h := exp_add_of_commute hc
      rw [← add_smul, show toReal Δt + (k : ℝ) * toReal Δt = (((k + 1 : ℕ) : ℝ)) * toReal Δt
        by push_cast; ring] at h
      rw [Matrix.mulVec_mulVec]
      exact congrArg (· *ᵥ x₀) h
    rw [hexp, Function.iterate_succ_apply']
    -- the run's step is `timePointStepFloat`, its matrix bound once
    exact Reduce.reduce_outer (sys.timePointStepFloat Δt η' _) ρ
      (sys.timePointStepFloat_outer hadm _ ih)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
