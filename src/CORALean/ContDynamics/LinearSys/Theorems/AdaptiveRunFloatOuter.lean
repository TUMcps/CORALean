module

public import CORALean.ContDynamics.LinearSys.Operations.AdaptiveRunFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AdaptiveStepFloatOuter

@[expose] public section

/-!
# An adaptive float run covers what is left of the horizon, soundly

[1, Alg. 1]'s loop, by induction on the iterations: each step's window starts where the state
stands and ends at the next state's time, clipped to `t_f`, so a time past
the window is past the next state and the rest of the run covers it. A run
ending with iterations to spare has reached `t_f`. Soundness is
`adaptiveStepFloat_outer` at each step, its time shifted back by `t₀`.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `t₀` – start time
* `tf` – final time
* `options` – adaptive options

## Hypotheses
* none

## Conclusion
* a successful run covers the rest of the horizon and its windows hold every run

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful run from a state holding the invariant has either already
reached `t_f`, or its windows cover `[t₀ + t_i, t₀ + t_f]`; and each window
holds every run at every time of it. -/
theorem LinearSys.adaptiveRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {t₀ tf : ℚ} {options : LinearSys.AdaptiveOptions 𝕋} : -- --- CONCL ---
    ∀ {k : ℕ} {s : LinearSys.AdaptiveState 𝕋 n} {steps : List (LinearSys.AdaptiveStepInfo 𝕋 n)},
      sys.adaptiveRunFloat X₀ V t₀ tf options k s = some steps → sys.AdaptiveInvariant V s →
      ((tf : ℝ) ≤ s.t ∨ ∀ t ∈ Set.Icc ((t₀ : ℝ) + s.t) ((t₀ : ℝ) + tf),
          ∃ r ∈ steps, t ∈ Set.Icc (r.tStart : ℝ) r.tEnd) ∧
        ∀ r ∈ steps, ∀ {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 (tf : ℝ)) X₀.construct U x u →
          U ⊆ V.construct → ∀ t ∈ Set.Icc (r.tStart : ℝ) r.tEnd,
            x (t - t₀) ∈ r.R.construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro s steps h _
    simp only [LinearSys.adaptiveRunFloat] at h
    split_ifs at h with hle
    obtain rfl := (Option.some.inj h).symm
    exact ⟨Or.inl (by exact_mod_cast hle), by simp⟩
  | succ k ih =>
    intro s steps h hinv
    simp only [LinearSys.adaptiveRunFloat] at h
    split_ifs at h with hle
    · obtain rfl := (Option.some.inj h).symm
      exact ⟨Or.inl (by exact_mod_cast hle), by simp⟩
    -- one step, then the rest of the run from the state it reached
    cases hstep : sys.adaptiveStepFloat X₀ V t₀ tf options s with
    | none => simp [hstep] at h
    | some rs =>
      obtain ⟨r, s'⟩ := rs
      simp only [hstep, Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      obtain ⟨hinv', hlt, hrs, hre, hsound⟩ := sys.adaptiveStepFloat_outer hinv _ _ hstep
      obtain ⟨hcov, hsnd⟩ := ih hrest hinv'
      have hre' : (r.tEnd : ℝ) = t₀ + min (s'.t : ℝ) tf := by rw [hre]; push_cast; rfl
      have hrs' : (r.tStart : ℝ) = t₀ + s.t := by rw [hrs]; push_cast; rfl
      refine ⟨Or.inr fun t ht => ?_, fun r' hr' U x u traj hUV t ht => ?_⟩
      · -- inside this step's window, or past the next state's time
        by_cases htle : t ≤ t₀ + min (s'.t : ℝ) tf
        · exact ⟨r, List.mem_cons_self .., by rw [hrs', hre']; exact ⟨ht.1, htle⟩⟩
        · have hst : (s'.t : ℝ) < tf := by
            by_contra hc
            exact htle (by rw [min_eq_right (not_lt.mp hc)]; exact ht.2)
          rw [min_eq_left hst.le] at htle
          rcases hcov with hc | hc
          · exact absurd hc (not_le.mpr hst)
          · obtain ⟨r', hr', hmem⟩ := hc t ⟨(not_le.mp htle).le, ht.2⟩
            exact ⟨r', List.mem_cons_of_mem _ hr', hmem⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · rw [hrs', hre'] at ht
          exact hsound traj hUV (t - t₀) ⟨by linarith [ht.1],
            by linarith [ht.2, min_le_left (s'.t : ℝ) tf]⟩
            (by linarith [ht.2, min_le_right (s'.t : ℝ) tf])
        · exact hsnd r' hr' traj hUV t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
