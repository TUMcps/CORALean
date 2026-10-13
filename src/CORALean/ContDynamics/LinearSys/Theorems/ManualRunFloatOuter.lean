import CORALean.ContDynamics.LinearSys.Operations.ManualRunFloat
import CORALean.ContDynamics.LinearSys.Theorems.ManualStepFloatOuter

/-!
# A float run of `Alg. 1` holds every run in every window

Induction on the iterations of [1, Alg. 1], each one `manualStepFloat_outer`: from a state
holding the invariant at `t_k`, the `j`-th window returned holds every run over
`[t_k + jΔt, t_k + (j+1)Δt]`.

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

/-- `K` iterations from a state holding the invariant return `K` windows, the `j`-th holding
every run over `[t_k + jΔt, t_k + (j+1)Δt]`. -/
theorem LinearSys.manualRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {Δt : 𝕋} {η ρ : ℕ} (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) :
    ∀ {K : ℕ} {s : LinearSys.ManualStateFloat 𝕋 n} {Rs : List (Zonotope (Vec 𝕋 n))},
      sys.manualRunFloat X₀ V Δt η ρ K s = some Rs → sys.ManualInvariantFloat X₀ V s →
      Rs.length = K ∧ ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 T) X₀.construct U x u →
        U ⊆ V.construct → ∀ (j : ℕ) (hj : j < Rs.length),
          ∀ t ∈ Set.Icc ((s.t : ℝ) + j * toReal Δt) (s.t + (j + 1) * toReal Δt), t ≤ T →
            x t ∈ Rs[j].construct := by -- --- PROOF ---
  intro K
  induction K with
  | zero =>
    intro s Rs h _
    obtain rfl := (Option.some.inj h).symm
    exact ⟨rfl, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ K ih =>
    intro s Rs h hinv
    simp only [LinearSys.manualRunFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s', R⟩, hstep, Rs', hrest, h⟩ := h
    obtain rfl := (Option.some.inj h).symm
    -- one iteration, then the rest of the run from the state it reached
    obtain ⟨hinv', ht', hwin⟩ := sys.manualStepFloat_outer hΔt hη hstep hinv
    obtain ⟨hlen, hsnd⟩ := ih hrest hinv'
    refine ⟨by simp [hlen], fun {T U x u} traj hUV j hj t ht htT => ?_⟩
    cases j with
    | zero =>
      exact hwin traj hUV t ⟨by simpa using ht.1, by rw [ht']; simpa using ht.2⟩ htT
    | succ j =>
      have hj' : j < Rs'.length := by simpa using hj
      refine hsnd traj hUV j hj' t ⟨?_, ?_⟩ htT
      · rw [ht']; push_cast at ht; linarith [ht.1]
      · rw [ht']; push_cast at ht; linarith [ht.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
