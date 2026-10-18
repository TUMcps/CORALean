module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStepFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.OrderStepFloatOuter

@[expose] public section

/-!
# One adaptively-tuned float step holds every run of the real system

The step `adaptStepFloat` returns is a step of `orderStepFloat` at the time step the tuning chose,
reduced; `orderStepFloat_outer` places every run, and the tuning, whatever it chose, enters only
through that time step. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The step the state's order picks of the two the tuning computed is a step of that order. -/
theorem aux_adaptStep_pick {fm : NonlinearSys.FloatHessModel 𝕋 n m} {U : Zonotope (Vec 𝕋 m)}
    {options : LinearSys.ReachOptions 𝕋} {Δ : 𝕋} {R : Zonotope (Vec 𝕋 n)} {κ : ℕ}
    {F₁ F₂ : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)}
    (hF₁ : fm.orderStepFloat 1 U { options with Δt := Δ } R = some F₁)
    (hF₂ : fm.orderStepFloat 2 U { options with Δt := Δ } R = some F₂) : -- --- STMT ---
    fm.orderStepFloat κ U { options with Δt := Δ } R =
      some (if κ = 1 then F₁ else F₂) := by -- --- PROOF ---
  by_cases hκ : κ = 1
  · -- the first order
    simp only [hκ, if_true] at *
    exact hF₁
  · -- any other order is the second
    unfold NonlinearSys.FloatHessModel.orderStepFloat at hF₂ ⊢
    simpa [hκ] using hF₂

/-- The step at the tuned time step `Δ`, reduced, holds every run. -/
theorem aux_adaptStep_finish {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {Δ : 𝕋}
    {t₀ : ℚ} {R : Zonotope (Vec 𝕋 n)} {F : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)} {κ : ℕ}
    (hF : fm.orderStepFloat κ U { options with Δt := Δ } R = some F) : -- --- STMT ---
    t₀ < t₀ + ToRat.toRat Δ ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
      sys.IsTrajectory (S := 𝒮) (Set.Icc 0 ((t₀ + ToRat.toRat Δ - t₀ : ℚ) : ℝ))
        R.construct U.construct x u y →
      (∀ t ∈ Set.Icc 0 ((t₀ + ToRat.toRat Δ - t₀ : ℚ) : ℝ),
          x t ∈ (Reduce.reduce F.1 options.ρ).construct) ∧
        x ((t₀ + ToRat.toRat Δ - t₀ : ℚ) : ℝ) ∈
          (Reduce.reduce F.2 options.ρ).construct := by -- --- PROOF ---
  -- the time of the step, exactly, is the step size
  have hcast : ((t₀ + ToRat.toRat Δ - t₀ : ℚ) : ℝ) = toReal Δ := by
    rw [add_sub_cancel_left, ToRat.toReal_toRat]
  obtain ⟨hpos, hout⟩ := h.orderStepFloat_outer _ _ hF
  refine ⟨?_, fun {x u y} traj => ?_⟩
  · -- a positive step size is a positive exact time
    have h1 : (0 : ℝ) < ((ToRat.toRat Δ : ℚ) : ℝ) := by rwa [ToRat.toReal_toRat]
    have h2 : (0 : ℚ) < ToRat.toRat Δ := by exact_mod_cast h1
    linarith
  · -- reducing the sets keeps the run in them
    rw [hcast] at traj ⊢
    obtain ⟨hwin, hend⟩ := hout traj
    exact ⟨fun t ht => Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _ (hwin t ht),
      Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _ hend⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time advances, and every run of `sys` over the step from `R` under inputs in `U` is in
`R(τ)` over the step and in `R(t_{k+1})` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.adaptStepFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {ζδ ζh ζZ ζK : 𝕋}
    {prec bis fuel : ℕ} {s : NonlinearSys.AdaptState 𝒵[𝕋] n ℚ 𝕋} : -- --- STMT ---
    ∀ s' ∈ fm.adaptStepFloat U options ζδ ζh ζZ ζK prec bis fuel s,
      s.t < s'.t ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := 𝒮) (Set.Icc 0 ((s'.t - s.t : ℚ) : ℝ))
          s.R.construct U.construct x u y →
        (∀ t ∈ Set.Icc 0 ((s'.t - s.t : ℚ) : ℝ), x t ∈ s'.Rτ.construct) ∧
          x ((s'.t - s.t : ℚ) : ℝ) ∈ s'.R.construct := by -- --- PROOF ---
  intro s' (hstep : fm.adaptStepFloat U options ζδ ζh ζZ ζK prec bis fuel s = some s')
  unfold NonlinearSys.FloatHessModel.adaptStepFloat at hstep
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨p1, hp1, F0, hF0, p2, hp2, F₁, hF₁, F₂, hF₂, hpure⟩ := hstep
  simp only [pure, Option.some.injEq] at hpure
  subst hpure
  -- the reported step is the one of the state's order
  exact aux_adaptStep_finish h (aux_adaptStep_pick hF₁ hF₂)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
