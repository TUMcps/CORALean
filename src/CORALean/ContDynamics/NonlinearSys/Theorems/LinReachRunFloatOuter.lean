module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachRunFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

@[expose] public section

/-!
# The float `linReach` loop holds every run over every step

Induction on the step count. The first step places the run over `[0, Δt]` and
at `Δt` (`linReachFloat_outer`); the run re-anchored at `Δt` (`Trajectory.shift`)
starts in the set that step returned, which is what the rest of the loop was run
from, so the hypothesis places it over every later step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from
`R` under inputs in `U` is, at every time of step `j`, in the `j`-th of them. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachRunFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {alg : NonlinearSys.LinReachAlg} {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} :
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.linReachRunFloat alg U options k R = some Rs → Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
          sys.Trajectory (S := 𝒮)
            (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.construct U.construct x u →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.Δt)
            (((j : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[j].construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro R Rs hRs
    simp only [NonlinearSys.FloatHessModel.linReachRunFloat, Option.some.injEq] at hRs
    subst hRs
    exact ⟨rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro R Rs hRs
    simp only [NonlinearSys.FloatHessModel.linReachRunFloat, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hRs
    obtain ⟨⟨Rτ, Rt⟩, hstep, rest, hrest, hpure⟩ := hRs
    simp only [pure, Option.some.injEq] at hpure
    subst hpure
    obtain ⟨hΔt, hout⟩ := h.linReachFloat_outer hstep
    obtain ⟨hlen, hrestout⟩ := ih hrest
    set Δt := toReal options.Δt
    refine ⟨by simp [hlen], fun {x u} traj j hj t ht => ?_⟩
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
      have shifted := traj.shift (R₀' := Rt.construct) hmaps hend
      have hj' : j < rest.length := by simpa using hj
      have key := hrestout shifted j hj' (t - Δt)
        ⟨by push_cast at ht; linarith [ht.1], by push_cast at ht; linarith [ht.2]⟩
      simpa using key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
