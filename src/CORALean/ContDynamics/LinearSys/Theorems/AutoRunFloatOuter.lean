import CORALean.ContDynamics.LinearSys.Operations.AutoRunFloat
import CORALean.ContDynamics.LinearSys.Theorems.AutoStepFloatOuter

/-!
# `autoRunFloat` holds every run over every time it covers

Induction on the iteration budget of [1, Alg. 2]'s loop: `autoStepFloat_outer` takes one
iteration from a state holding the invariant to one holding it later in time, with the window
covering that iteration's times, and the rest of the run covers the times after. Every time in
`[t_k, t_end']` the run reached, if it advanced at all, is in some window it returned.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Up to `K` iterations from a state holding the invariant reach one holding it, no earlier,
and if time advanced, every run over any time it covers is in one of the returned windows. -/
theorem LinearSys.autoRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)} {tend : 𝕋}
    {εmax ζ : ℚ} {ηmax fuel : ℕ} :
    ∀ {K : ℕ} {s s' : LinearSys.AutoStateFloat 𝕋 n} {Ws : List (ℚ × ℚ × Zonotope (Vec 𝕋 n))},
      sys.autoRunFloat X₀ V tend εmax ζ ηmax fuel K s = some (s', Ws) →
      sys.AutoInvariantFloat X₀ V s →
      sys.AutoInvariantFloat X₀ V s' ∧ s.t ≤ s'.t ∧
        ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 T) X₀.construct U x u →
          U ⊆ V.construct → s.t < s'.t → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ T →
            ∃ w ∈ Ws, t ∈ Set.Icc (w.1 : ℝ) w.2.1 ∧ x t ∈ w.2.2.construct := by -- --- PROOF ---
  intro K
  induction K with
  | zero =>
    intro s s' Ws h hinv
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact ⟨hinv, le_rfl, fun _ _ hlt => absurd hlt (lt_irrefl _)⟩
  | succ K ih =>
    intro s s' Ws h hinv
    simp only [LinearSys.autoRunFloat] at h
    split_ifs at h with hend
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      exact ⟨hinv, le_rfl, fun _ _ hlt => absurd hlt (lt_irrefl _)⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s1, R⟩, hstep, ⟨s2, Rs⟩, hrest, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (by simpa using h)).symm
      -- one iteration, then the rest of the run from the state it reached
      obtain ⟨hinv1, hlt1, hwin⟩ := sys.autoStepFloat_outer hstep hinv
      obtain ⟨hinv2, hle2, hrun⟩ := ih hrest hinv1
      refine ⟨hinv2, hlt1.le.trans hle2, fun {T U x u} traj hUV _ t ht htT => ?_⟩
      by_cases hts : t ≤ s1.t
      · exact ⟨_, List.mem_cons_self .., ⟨ht.1, hts⟩, hwin traj hUV t ⟨ht.1, hts⟩ htT⟩
      · rw [not_le] at hts
        have hlt2 : s1.t < s'.t := by
          have : (s1.t : ℝ) < s'.t := lt_of_lt_of_le hts ht.2
          exact_mod_cast this
        obtain ⟨w, hw, hwt, hxw⟩ := hrun traj hUV hlt2 t ⟨hts.le, ht.2⟩ htT
        exact ⟨w, List.mem_cons_of_mem _ hw, hwt, hxw⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
