module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachPolyAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyAdaptiveFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# CORA's poly-adaptive algorithm, repaired, holds every run of the real system

`reachPolyAdaptiveFloat` from a state `s`, by induction on the number of steps: each step holds
every run from its start set over its window and at its end (`linReachPolyAdaptiveFloat_outer`), the
adaptive reductions only enlarge (`reduceAdaptive_outer`, and the restructuring and dependent
reductions likewise), and the run re-anchored at the step's end is a run from the next start set
(`IsTrajectory.shift`). So every run of the real system on `[0, t_N - t_0]` from `s.R` is, at each
time of step `j`'s window, in that step's time-interval set; the tuning, the tensor orders and the
reductions do not enter. The time never decreases.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `o` – adaptive options
* `maxPolyZonoRatio` – volume ratio above which the start set is restructured

## Hypotheses
* `h` – model encloses system
* `hfix` – the abstraction error's fixed point confines the runs
* `htrack` – the static error follows the factors of the start set, at every step size

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A run from a set is a run from any set holding it. -/
private theorem aux_prfa_mono_init {sys : NonlinearSys n m} {T : Set ℝ} {R₀ R₀' : Set (Vec ℝ n)}
    {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) T R₀ U x u y) (h : R₀ ⊆ R₀') :
    sys.IsTrajectory (S := ExactSet) T R₀' U x u y :=
  { traj with init := h traj.init }

omit [ToRat 𝕋] in
/-- Boxing the shortest dependent generators only grows the set. -/
private theorem aux_prfa_reduceOnlyDep_outer (R : PolyZonotope (Vec 𝕋 n)) (order p : ℕ) :
    R.toSet ⊆ (step_reduceOnlyDep R order p).toSet := by
  unfold step_reduceOnlyDep
  split_ifs
  · exact subset_rfl
  · exact PolyZonotope.reduceBy_outer R _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run of `sys` from `s.R` under inputs in `U`, over the time the steps cover, is in the
time-interval set of each step at the times of its window. -/
theorem NonlinearSys.FloatHessModel.Encloses.reachPolyAdaptiveFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (hfix : sys.HasFixedPointConfinement) {U : Zonotope (Vec 𝕋 m)}
    {o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋} {maxPolyZonoRatio : 𝕋}
    (htrack : ∀ (R : PolyZonotope (Vec 𝕋 n)) (Δt : 𝕋),
      fm.HasTrackedPassStaticError U ⟨⟨Δt, o.taylorTerms⟩, o.zonotopeOrder⟩ o.redFactor o.prec
        R) : -- --- CONCL ---
    ∀ (k : ℕ) {s : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n}
      {ss : List (NonlinearSys.LinReachPolyAdaptiveState 𝕋 n)},
      fm.reachPolyAdaptiveFloat U o maxPolyZonoRatio k s = some ss →
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
    simp only [NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat, Option.some.injEq] at hrun
    subst hrun
    exact ⟨le_rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro s ss hrun
    unfold NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat at hrun
    by_cases ht : ToRat.toRat o.endTol < o.tFinal - s.t ∧
        step_abortPolyAdaptive o s.t s.steps = false
    · -- the horizon is not reached: one step, its sets reduced, then the rest
      rw [if_pos ht] at hrun
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
      obtain ⟨s', hs', rest, hrest, hpure⟩ := hrun
      simp only [pure, Option.some.injEq] at hpure
      subst hpure
      generalize hs₀def : (if step_volumeRatioExceeds s.R maxPolyZonoRatio = true
          then { s with R := s.R.restructure } else s) = s₀ at hs'
      -- the step may start from the restructured set, which holds the start set
      have hR₀ : s.R.toSet ⊆ s₀.R.toSet := by
        rw [← hs₀def]
        split_ifs
        · exact PolyZonotope.restructure_outer s.R
        · exact subset_rfl
      set s'' := { s' with
        R := step_reduceOnlyDep (s'.R.reduceAdaptive o.redFactor o.prec) o.maxDepGenOrder o.prec,
        Rτ := s'.Rτ.reduceAdaptive (mulUp o.redFactor (nsmulUp 5 one)) o.prec } with hs''
      -- the step, and what the rest of the run guarantees from where it left off
      obtain ⟨hlt, hstep₀⟩ := h.linReachPolyAdaptiveFloat_outer hfix htrack _ hs'
      -- the times line up, and the step's guarantee is stated at the original start set
      have hs₀t : s₀.t = s.t := by
        rw [← hs₀def]
        split_ifs <;> rfl
      have hlt' : s.t < s''.t := by
        rw [← hs₀t]
        exact hlt
      have hΔeq : ((s'.t - s₀.t : ℚ) : ℝ) = ((s''.t - s.t : ℚ) : ℝ) := by rw [hs₀t]
      -- the step's guarantee, after the reductions
      have hstep : ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet) (Set.Icc 0 ((s''.t - s.t : ℚ) : ℝ)) s.R.toSet U.toSet x u
            y →
          (∀ t ∈ Set.Icc 0 ((s''.t - s.t : ℚ) : ℝ), x t ∈ s''.Rτ.toSet) ∧
            x ((s''.t - s.t : ℚ) : ℝ) ∈ s''.R.toSet := fun {x u y} traj => by
        have tr := aux_prfa_mono_init traj hR₀
        rw [← hΔeq] at tr
        have st := hstep₀ tr
        rw [hΔeq] at st
        exact ⟨fun t ht => PolyZonotope.reduceAdaptive_outer _ _ _ (st.1 t ht),
          aux_prfa_reduceOnlyDep_outer _ _ _
            (PolyZonotope.reduceAdaptive_outer _ _ _ st.2)⟩
      obtain ⟨hmono, hind⟩ := ih hrest
      rw [List.getLast_cons (List.cons_ne_nil _ _)]
      refine ⟨le_trans hlt'.le hmono, fun {x u y} traj j hj t ht' => ?_⟩
      -- the horizon is the first step plus the rest's
      set L := ((s'' :: rest).getLast (List.cons_ne_nil _ _)).t with hL
      have hΔ : (0 : ℝ) < ((s''.t - s.t : ℚ) : ℝ) := by
        exact_mod_cast sub_pos.mpr hlt'
      have hLs : ((L - s.t : ℚ) : ℝ) = ((s''.t - s.t : ℚ) : ℝ) + ((L - s''.t : ℚ) : ℝ) := by
        push_cast; ring
      have hL0 : (0 : ℝ) ≤ ((L - s''.t : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hmono
      -- the first step, on its own window
      have hsub : Set.Icc (0 : ℝ) ((s''.t - s.t : ℚ) : ℝ) ⊆ Set.Icc 0 ((L - s.t : ℚ) : ℝ) :=
        fun r hr => ⟨hr.1, le_trans hr.2 (by rw [hLs]; linarith)⟩
      obtain ⟨hwin, hend⟩ := hstep (traj.restrict hsub)
      cases j with
      | zero =>
        refine hwin t ⟨?_, ?_⟩
        · simpa using ht'.1
        · simpa using ht'.2
      | succ j =>
        -- the run re-anchored where the first step left it
        have hmaps : Set.MapsTo (fun r => ((s''.t - s.t : ℚ) : ℝ) + r)
            (Set.Icc 0 ((L - s''.t : ℚ) : ℝ)) (Set.Icc 0 ((L - s.t : ℚ) : ℝ)) :=
          fun r hr => ⟨by linarith [hr.1], by rw [hLs]; linarith [hr.2]⟩
        have shifted := traj.shift (R₀' := s''.R.toSet) hmaps (hsub ⟨hΔ.le, le_rfl⟩) hend
        have hj' : j < rest.length := by simpa using hj
        have key := hind shifted j hj' (t - ((s''.t - s.t : ℚ) : ℝ)) ⟨?_, ?_⟩
        · simpa using key
        · have := ht'.1
          simp only [List.getElem_cons_succ] at this
          push_cast at this ⊢
          linarith
        · have := ht'.2
          simp only [List.getElem_cons_succ] at this
          push_cast at this ⊢
          linarith
    · rw [if_neg ht] at hrun
      simp only [Option.some.injEq] at hrun
      subst hrun
      exact ⟨le_rfl, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
