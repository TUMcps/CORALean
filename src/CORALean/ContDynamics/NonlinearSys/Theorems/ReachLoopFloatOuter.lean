module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachLoopFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachLoopFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

@[expose] public section

/-!
# `reachLoopFloat` holds every run of the real system over every window

The counterpart of `reachAlgFloat_outer` with CORA's error loop in each step: every run of
`ẋ = f(x, u)` on `[0, tFinal - tStart]` from `X₀` under any input signal in `U`. `Reach.steps`
makes the horizon `N` steps exactly, and `aux_linReachLoopRunFloat_outer` does the rest; each step
holds whatever error guess it starts from, so the guess handed from step to step cannot affect it.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `params` – reachability parameters
* `options` – reachability options
* `enlarge` – enlargement of the error
* `fuel` – iteration bound
* `maxError` – largest admissible error, if any
* `step` – linear step

## Hypotheses
* `h` – model encloses system

## Conclusion
* every run lies in the returned set of its window
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from
`R` under inputs in `U` is, at every time of step `j`, in the `j`-th of them. -/
private theorem NonlinearSys.FloatHessModel.Encloses.aux_linReachLoopRunFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {maxError : Option (Vec 𝕋 n)} {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {err : Vec 𝕋 n} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.step_linReachLoopRunFloat U options enlarge fuel maxError step k R err = some Rs →
        Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet)
            (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.toSet U.toSet x u y →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.Δt)
            (((j : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[j].toSet := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro R err Rs hRs
    simp only [NonlinearSys.FloatHessModel.step_linReachLoopRunFloat, Option.some.injEq] at hRs
    subst hRs
    exact ⟨rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro R err Rs hRs
    simp only [NonlinearSys.FloatHessModel.step_linReachLoopRunFloat, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hRs
    obtain ⟨⟨Rτ, Rt, err'⟩, hstep, rest, hrest, hpure⟩ := hRs
    simp only [pure, Option.some.injEq] at hpure
    subst hpure
    obtain ⟨hΔt, hout⟩ := h.linReachLoopFloat_outer _ _ _ hstep
    obtain ⟨hlen, hrestout⟩ := ih hrest
    set Δt := toReal options.Δt
    refine ⟨by simp [hlen], fun {x u y} traj j hj t ht => ?_⟩
    -- the first step, on its own window
    have hsub : Set.Icc 0 Δt ⊆ Set.Icc 0 (((k + 1 : ℕ) : ℝ) * Δt) := fun s hs =>
      ⟨hs.1, le_trans hs.2 (by push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])⟩
    obtain ⟨hwin, hend⟩ := hout (traj.restrict hsub)
    cases j with
    | zero =>
      exact hwin t ⟨by simpa using ht.1, by simpa using ht.2⟩
    | succ j =>
      -- the run re-anchored at `Δt`, from where the first step left it
      have hmaps : Set.MapsTo (fun s => Δt + s) (Set.Icc 0 ((k : ℝ) * Δt))
          (Set.Icc 0 (((k + 1 : ℕ) : ℝ) * Δt)) := fun s hs =>
        ⟨by linarith [hs.1], by push_cast; linarith [hs.2]⟩
      have shifted := traj.shift (R₀' := Rt.toSet) hmaps (hsub ⟨hΔt.le, le_rfl⟩) hend
      have hj' : j < rest.length := by simpa using hj
      have key := hrestout shifted j hj' (t - Δt)
        ⟨by push_cast at ht; linarith [ht.1], by push_cast at ht; linarith [ht.2]⟩
      simpa using key


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order, every run on `[0, tFinal - tStart]` from
`X₀` under inputs in `U` is, at every time of window `k`, in the `k`-th set returned. -/
theorem NonlinearSys.FloatHessModel.Encloses.reachLoopFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {maxError : Option (Vec 𝕋 n)} {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ Rs ∈ fm.reachLoopFloat params options enlarge fuel maxError step,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.toSet
            params.U.toSet x u y →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].toSet := by -- --- PROOF ---
  intro Rs (hR : fm.reachLoopFloat params options enlarge fuel maxError step = some Rs)
  unfold NonlinearSys.FloatHessModel.reachLoopFloat at hR
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨N, hN, hrun⟩ := hR
  obtain ⟨-, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  obtain ⟨hlen, hout⟩ := h.aux_linReachLoopRunFloat_outer N hrun
  refine ⟨N, hNΔt, hlen, fun {x u y} traj => ?_⟩
  -- the horizon is `N` steps exactly
  rw [← hNΔt] at traj
  exact hout traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
