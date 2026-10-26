module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

@[expose] public section

/-!
# `reachAlgFloat` holds every run of the real system over every window

The counterpart of `FloatModel.Encloses.reachFloat_outer` at either `alg`, against the
same object: every run of `ẋ = f(x, u)` on `[0, tFinal - tStart]` from `X₀` under any
input signal in `U`. `Reach.steps` makes the horizon `N` steps exactly, and
`aux_linReachRunFloat_outer` does the rest.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `alg` – abstraction algorithm
* `params` – reachability parameters
* `options` – reachability options

## Hypotheses
* `h` – model encloses system

## Conclusion
* every run lies in the returned set of its window
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from
`R` under inputs in `U` is, at every time of step `j`, in the `j`-th of them. -/
private theorem NonlinearSys.FloatHessModel.Encloses.aux_linReachRunFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {alg : NonlinearSys.LinReachAlg} {U : Zonotope (Vec 𝕋 m)}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.aux_linReachRunFloat alg U options k R = some Rs → Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.construct U.construct x u y →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.Δt)
            (((j : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[j].construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro R Rs hRs
    simp only [NonlinearSys.FloatHessModel.aux_linReachRunFloat, Option.some.injEq] at hRs
    subst hRs
    exact ⟨rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro R Rs hRs
    simp only [NonlinearSys.FloatHessModel.aux_linReachRunFloat, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hRs
    obtain ⟨⟨Rτ, Rt⟩, hstep, rest, hrest, hpure⟩ := hRs
    simp only [pure, Option.some.injEq] at hpure
    subst hpure
    obtain ⟨hΔt, hout⟩ := h.linReachFloat_outer _ _ hstep
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
      have shifted := traj.shift (R₀' := Rt.construct) hmaps (hsub ⟨hΔt.le, le_rfl⟩) hend
      have hj' : j < rest.length := by simpa using hj
      have key := hrestout shifted j hj' (t - Δt)
        ⟨by push_cast at ht; linarith [ht.1], by push_cast at ht; linarith [ht.2]⟩
      simpa using key


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order, every run on `[0, tFinal - tStart]` from
`X₀` under inputs in `U` is, at every time of window `k`, in the `k`-th set returned. -/
theorem NonlinearSys.FloatHessModel.Encloses.reachAlgFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {alg : NonlinearSys.LinReachAlg}
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ fm.reachAlgFloat alg params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            params.U.construct x u y →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (hR : fm.reachAlgFloat alg params options = some Rs)
  unfold NonlinearSys.FloatHessModel.reachAlgFloat at hR
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨N, hN, hrun⟩ := hR
  obtain ⟨-, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  obtain ⟨hlen, hout⟩ := h.aux_linReachRunFloat_outer N hrun
  refine ⟨N, hNΔt, hlen, fun {x u y} traj => ?_⟩
  -- the horizon is `N` steps exactly
  rw [← hNΔt] at traj
  exact hout traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
