module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptiveLoop
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAtOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.IsTrajectoryShift

@[expose] public section

/-!
# The adaptive time loop holds every certified run

A run `x` of the DAE on `[0, T]`, `t_f ≤ T`, certified at every step the loop takes by the
errors and step the adaptive pass settled on (`LinPoint.Certifies`, the hypotheses of
`linReach_outer`; [1, Alg. 1]), is in the union the loop returns up to the time it reaches. By
induction on the fuel, on a state `(t, R(t), R_union)` as for `reachLoop_outer`. The tuning
cannot affect it: the certificate is asked of whatever step the pass chose, and the loop only
takes steps that are positive and end by `t_f`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The loop of `reach_adaptive` from a state whose `R` holds the run: the run up to the time
reached is in the union returned. -/
theorem NonlinDASys.reachAdaptiveLoop_outer (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (U : Zonotope (Vec ℝ m)) (tFinal tol : ℝ)
    (k fuelErr fuelHalf : ℕ)
    {R0 : Zonotope (Vec ℝ n)} {Tmax : ℝ} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p}
    {u : ℝ → Vec ℝ m}
    (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Tmax) R0 U x y u) (hT : tFinal ≤ Tmax)
    (hcert : ∀ (st : NonlinDASys.AdaptState n p) (h : ℝ) (lastStep : Bool)
      (pass : NonlinDASys.AdaptPass n p), 0 ≤ st.t → x st.t ∈ st.R.construct →
      sys.linReachAdaptive T st.R U (k + 2) fuelErr fuelHalf st.adm_x st.adm_y h lastStep
        = some pass → 0 < pass.Δt → pass.Δt ≤ tFinal - st.t →
      (pass.linPoint (T.taylor st.R)).Certifies sys U pass.Δt k
        (fun s => x (st.t + s)) (fun s => y (st.t + s)) (fun s => u (st.t + s))) :
    ∀ (fuel : ℕ) (st : NonlinDASys.AdaptState n p) (Runion : Set (Vec ℝ n)),
      0 ≤ st.t → x st.t ∈ st.R.construct →
      (0 < st.t → ∀ t ∈ Set.Icc 0 st.t, x t ∈ Runion) → st.t ≤ tFinal →
      ∀ res tEnd, sys.reachAdaptiveLoop T U tFinal tol (k + 2) fuelErr fuelHalf fuel st Runion
          = some (res, tEnd) → 0 < tEnd → ∀ t ∈ Set.Icc 0 tEnd, x t ∈ res := by -- --- PROOF ---
  -- induction on the fuel, over all states holding the run
  intro fuel
  induction fuel with
  | zero =>
    intro st Runion h0 hx hcov hle res tEnd hres hpos
    simp only [NonlinDASys.reachAdaptiveLoop] at hres
    split at hres
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
      exact hcov hpos
    · simp at hres
  | succ fuel ih =>
    -- one more step: the pass, the shifted run, and the loop from the next state
    intro st Runion h0 hx hcov hle res tEnd hres hpos
    simp only [NonlinDASys.reachAdaptiveLoop] at hres
    split at hres
    · next htol =>
      split at hres
      · simp at hres
      · next pass hpass =>
        split at hres
        · next hguard =>
          -- the run counted from `t`, started in `R`, is a run on `[0, Δt]` the certificate covers
          have hab : st.t + pass.Δt ≤ Tmax := by linarith [hguard.2]
          have run := traj.shift (a := st.t) (b := pass.Δt) h0 hab hx
          obtain ⟨hnext, hint⟩ := NonlinDASys.IsTrajectory.linReachAt_outer run hguard.1
            (hcert st _ _ pass h0 hx hpass hguard.1 hguard.2)
          -- the loop from `t + Δt`, with the time-interval set joined to the union
          refine ih _ _ (by simp only; linarith [hguard.1]) ?_ ?_ (by
              simp only; linarith [hguard.2]) res tEnd hres hpos
          · exact hnext
          · intro _ t ht
            by_cases hlt : t < st.t
            · exact Or.inl (hcov (lt_of_le_of_lt ht.1 hlt) t ⟨ht.1, hlt.le⟩)
            · refine Or.inr ?_
              have hs : t - st.t ∈ Set.Icc 0 pass.Δt :=
                ⟨by linarith, by linarith [ht.2]⟩
              have := (hint _ hs).1
              rwa [add_sub_cancel] at this
        · simp at hres
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
      exact hcov hpos

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
