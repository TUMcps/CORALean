module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinRunAtFloatOuter
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

@[expose] public section

/-!
# `reachFloat` holds every run of the real system over every window

The float counterpart of `WithSteps.reachUnion_outer`, against the same object:
every run of `ẋ = f(x, u)` on `[0, tFinal - tStart]` from `X₀` under any input
signal in `U`. `Reach.steps` makes the horizon `N` steps exactly, and
`aux_relinRunFloat_outer` does the rest. What `reachUnion_outer` is handed as
certificates and checks as confinement, `FloatModel.Encloses` and the run's own
region checks supply.

## Inputs
* `fm` – float model
* `sys` – system
* `params` – reachability parameters
* `options` – reachability options

## Hypotheses
* `h` – model encloses system

## Conclusion
* every run lies in the returned set of its window
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from
`R` under inputs in `U` is, at every time of step `j`, in the `j`-th of them: the
re-linearization loop at its own `linPointFloat`. -/
private theorem NonlinearSys.FloatModel.Encloses.aux_relinRunFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} :
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.step_relinRunFloat U options k R = some Rs → Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.construct U.construct x u y →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.Δt)
            (((j : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[j].construct :=
  fun k _ _ hrun => h.relinRunAtFloat_outer k hrun


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys`, every run on `[0, tFinal - tStart]` from `X₀` under
inputs in `U` is, at every time of window `k`, in the `k`-th set `reachFloat` returns. -/
theorem NonlinearSys.FloatModel.Encloses.reachFloat_outer {fm : NonlinearSys.FloatModel 𝕋 n m}
    {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ fm.reachFloat params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            params.U.construct x u y →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (hR : fm.reachFloat params options = some Rs)
  unfold NonlinearSys.FloatModel.reachFloat at hR
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨N, hN, hrun⟩ := hR
  obtain ⟨-, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  obtain ⟨hlen, hout⟩ := h.aux_relinRunFloat_outer N hrun
  refine ⟨N, hNΔt, hlen, fun {x u y} traj => ?_⟩
  -- the horizon is `N` steps exactly
  rw [← hNΔt] at traj
  exact hout traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
