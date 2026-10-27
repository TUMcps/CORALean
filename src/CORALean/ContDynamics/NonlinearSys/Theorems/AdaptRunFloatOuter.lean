module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRunFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.AdaptStepFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

@[expose] public section

/-!
# The adaptive float loop holds every run of the real system

A run of `ẋ = f(x, u)` from `R` under inputs in `U` over the whole horizon is, over each step, a
run of that step re-anchored at the step's start (`IsTrajectory.shift`), so `adaptStepFloat_outer`
applies to each in turn. The steps' lengths are whatever the tuning chose; only their sum, the
horizon, enters. See [1].

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `options` – reachability options
* `ζδ` – first tuning constant
* `ζh` – second tuning constant
* `ζZ` – third tuning constant
* `ζK` – fourth tuning constant
* `prec` – precision
* `bis` – bisection depth
* `fuel` – iteration bound
* `tend` – final time

## Hypotheses
* `h` – model encloses system

## Conclusion
* every run of the system lies in the sets of its step

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run's states advance in time, and every run of `sys` from `R` under inputs in `U` over
the horizon they cover is, at every time of step `j`, in the `j`-th state's `R(τ)`. Step `j` is
`[t_j, t_{j+1}]` of `s :: ss`. -/
theorem NonlinearSys.FloatHessModel.Encloses.adaptRunFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {ζδ ζh ζZ ζK : 𝕋}
    {prec bis fuel : ℕ} {tend : ℚ} : -- --- CONCL ---
    ∀ (k : ℕ) {s : NonlinearSys.AdaptState 𝒵[𝕋] n ℚ 𝕋}
      {ss : List (NonlinearSys.AdaptState 𝒵[𝕋] n ℚ 𝕋)},
      fm.adaptRunFloat U options ζδ ζh ζZ ζK prec bis fuel tend k s = some ss →
      s.t ≤ ((s :: ss).getLast (List.cons_ne_nil _ _)).t ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((((s :: ss).getLast (List.cons_ne_nil _ _)).t - s.t : ℚ) : ℝ))
            s.R.construct U.construct x u y →
          ∀ (j : ℕ) (hj : j < ss.length), ∀ t ∈ Set.Icc
            ((((s :: ss)[j]'(Nat.lt_succ_of_lt hj)).t - s.t : ℚ) : ℝ) ((ss[j].t - s.t : ℚ) : ℝ),
            x t ∈ ss[j].Rτ.construct := by -- --- PROOF ---
  intro k
  -- induction on the iteration count, for every start state
  induction k with
  | zero =>
    intro s ss hrun
    simp only [NonlinearSys.FloatHessModel.adaptRunFloat, Option.some.injEq] at hrun
    subst hrun
    exact ⟨le_rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro s ss hrun
    unfold NonlinearSys.FloatHessModel.adaptRunFloat at hrun
    split_ifs at hrun with ht
    · -- the horizon is not reached: one step, then the rest
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
      obtain ⟨s', hs', rest, hrest, hpure⟩ := hrun
      simp only [pure, Option.some.injEq] at hpure
      subst hpure
      -- the step, and what the rest of the run guarantees from where it left off
      obtain ⟨hlt, hstep⟩ := h.adaptStepFloat_outer _ hs'
      obtain ⟨hmono, hind⟩ := ih hrest
      rw [List.getLast_cons (List.cons_ne_nil _ _)]
      refine ⟨le_trans hlt.le hmono, fun {x u y} traj j hj t ht' => ?_⟩
      -- the horizon is the first step plus the rest's
      set L := ((s' :: rest).getLast (List.cons_ne_nil _ _)).t with hL
      have hΔ : (0 : ℝ) < ((s'.t - s.t : ℚ) : ℝ) := by
        exact_mod_cast sub_pos.mpr hlt
      have hLs : ((L - s.t : ℚ) : ℝ) = ((s'.t - s.t : ℚ) : ℝ) + ((L - s'.t : ℚ) : ℝ) := by
        push_cast; ring
      have hL0 : (0 : ℝ) ≤ ((L - s'.t : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hmono
      -- the first step, on its own window
      have hsub : Set.Icc (0 : ℝ) ((s'.t - s.t : ℚ) : ℝ) ⊆ Set.Icc 0 ((L - s.t : ℚ) : ℝ) :=
        fun r hr => ⟨hr.1, le_trans hr.2 (by rw [hLs]; linarith)⟩
      obtain ⟨hwin, hend⟩ := hstep (traj.restrict hsub)
      cases j with
      | zero =>
        refine hwin t ⟨?_, ?_⟩
        · simpa using ht'.1
        · simpa using ht'.2
      | succ j =>
        -- the run re-anchored where the first step left it
        have hmaps : Set.MapsTo (fun r => ((s'.t - s.t : ℚ) : ℝ) + r)
            (Set.Icc 0 ((L - s'.t : ℚ) : ℝ)) (Set.Icc 0 ((L - s.t : ℚ) : ℝ)) :=
          fun r hr => ⟨by linarith [hr.1], by rw [hLs]; linarith [hr.2]⟩
        have shifted := traj.shift (R₀' := s'.R.construct) hmaps (hsub ⟨hΔ.le, le_rfl⟩) hend
        have hj' : j < rest.length := by simpa using hj
        have key := hind shifted j hj' (t - ((s'.t - s.t : ℚ) : ℝ)) ⟨?_, ?_⟩
        · simpa using key
        · have := ht'.1
          simp only [List.getElem_cons_succ] at this
          push_cast at this ⊢
          linarith
        · have := ht'.2
          simp only [List.getElem_cons_succ] at this
          push_cast at this ⊢
          linarith
    · simp only [Option.some.injEq] at hrun
      subst hrun
      exact ⟨le_rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
