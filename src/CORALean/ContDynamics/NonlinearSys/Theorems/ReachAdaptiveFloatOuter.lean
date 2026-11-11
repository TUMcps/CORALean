module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachAdaptiveFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# CORA's adaptive algorithm, repaired, holds every run of the real system

`reachAdaptiveFloat` from a state `s`, by induction on the number of steps: each step holds every
run from its start set over its window and at its end (`linReachAdaptiveFloat_outer`), the
adaptive reductions only enlarge (`reduceAdaptive_outer`), and the run re-anchored at the step's
end is a run from the next start set (`IsTrajectory.shift`). So every run of the real system on
`[0, t_N - t_0]` from `s.R` is, at each time of step `j`'s window, in that step's time-interval
set; the tuning, the tensor orders and the reductions do not enter. The time never decreases.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `o` – adaptive options

## Hypotheses
* `h` – model encloses system
* `hfix` – the abstraction error's fixed point confines the runs

## Conclusion
* every run of the real system lies in the time-interval set of the step whose window holds it
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run of `sys` from `s.R` under inputs in `U`, over the time the steps cover, is in the
time-interval set of each step at the times of its window. -/
theorem NonlinearSys.FloatHessModel.Encloses.reachAdaptiveFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (hfix : sys.HasFixedPointConfinement) {U : Zonotope (Vec 𝕋 m)}
    {o : NonlinearSys.LinReachAdaptiveOptions 𝕋} : -- --- CONCL ---
    ∀ (k : ℕ) {s : NonlinearSys.LinReachAdaptiveState 𝕋 n}
      {ss : List (NonlinearSys.LinReachAdaptiveState 𝕋 n)},
      fm.reachAdaptiveFloat U o k s = some ss →
      s.t ≤ ((s :: ss).getLast (List.cons_ne_nil _ _)).t ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet)
            (Set.Icc 0 ((((s :: ss).getLast (List.cons_ne_nil _ _)).t - s.t : ℚ) : ℝ))
            s.R.toSet U.toSet x u y →
          ∀ (j : ℕ) (hj : j < ss.length), ∀ t ∈ Set.Icc
            ((((s :: ss)[j]'(Nat.lt_succ_of_lt hj)).t - s.t : ℚ) : ℝ) ((ss[j].t - s.t : ℚ) : ℝ),
            x t ∈ ss[j].Rτ.toSet := by -- --- PROOF ---
  intro k
  -- induction on the step count, for every start state
  induction k with
  | zero =>
    intro s ss hrun
    simp only [NonlinearSys.FloatHessModel.reachAdaptiveFloat, Option.some.injEq] at hrun
    subst hrun
    exact ⟨le_rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro s ss hrun
    unfold NonlinearSys.FloatHessModel.reachAdaptiveFloat at hrun
    split_ifs at hrun with ht
    · -- the horizon is not reached: one step, its sets reduced, then the rest
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
      obtain ⟨s₀, hs₀, rest, hrest, hpure⟩ := hrun
      simp only [pure, Option.some.injEq] at hpure
      subst hpure
      set s' := { s₀ with
        R := s₀.R.reduceAdaptive o.redFactor o.prec,
        Rτ := s₀.Rτ.reduceAdaptive (mulUp o.redFactor (nsmulUp 5 one)) o.prec }
      -- the step, and what the rest of the run guarantees from where it left off
      obtain ⟨hlt, hstep₀⟩ := h.linReachAdaptiveFloat_outer hfix _ hs₀
      have hstep : ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet) (Set.Icc 0 ((s'.t - s.t : ℚ) : ℝ)) s.R.toSet U.toSet x u
            y →
          (∀ t ∈ Set.Icc 0 ((s'.t - s.t : ℚ) : ℝ), x t ∈ s'.Rτ.toSet) ∧
            x ((s'.t - s.t : ℚ) : ℝ) ∈ s'.R.toSet := fun traj =>
        ⟨fun t ht => Zonotope.reduceAdaptive_outer _ _ _ ((hstep₀ traj).1 t ht),
          Zonotope.reduceAdaptive_outer _ _ _ (hstep₀ traj).2⟩
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
        have shifted := traj.shift (R₀' := s'.R.toSet) hmaps (hsub ⟨hΔ.le, le_rfl⟩) hend
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
