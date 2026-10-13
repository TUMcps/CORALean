import CORALean.ContDynamics.NonlinearSys.Operations.SplitReach
import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

/-!
# Splitting loses no start: `splitReach_outer`

[1, Fig. 1]'s splitting is sound because the two halves cover what they split,
`Zonotope.split_union`, and nothing else: whatever `step` guarantees for every start
in the set it accepted, `splitReach` guarantees for every start in `R`, through
whichever segment came from the half holding that start.

`P x S` is that guarantee — "every run from `x` stays in `S` over the step" being
the intended one — and is left abstract: the step is the caller's, and so is what
it promises. Induction on the fuel, the two halves as the two hypotheses.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {β : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `step` promises for every start in a set it accepts, `splitReach` promises for
every start in `R`, through one of the segments it returns. -/
theorem NonlinearSys.splitReach_outer (step : Real.Zonotope (Vec ℝ n) → Option β)
    (pick : (R : Real.Zonotope (Vec ℝ n)) → Option (Fin R.h))
    (P : Vec ℝ n → β → Prop)
    (hstep : ∀ R S, step R = some S → ∀ x ∈ R.construct, P x S) :
    ∀ (fuel : ℕ) (R : Real.Zonotope (Vec ℝ n)) (l : List β),
      NonlinearSys.splitReach step pick fuel R = some l →
        ∀ x ∈ R.construct, ∃ S ∈ l, P x S := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro R l h; simp [NonlinearSys.splitReach] at h
  | succ fuel ih =>
    intro R l h x hx
    simp only [NonlinearSys.splitReach] at h
    rcases hs : step R with _ | S
    · rw [hs] at h
      rcases hp : pick R with _ | j
      · rw [hp] at h; exact absurd h (by simp)
      · rw [hp] at h
        simp only at h
        rcases h₁ : NonlinearSys.splitReach step pick fuel (R.split j).1 with _ | l₁
        · rw [h₁] at h; exact absurd h (by simp)
        rcases h₂ : NonlinearSys.splitReach step pick fuel (R.split j).2 with _ | l₂
        · rw [h₁, h₂] at h; exact absurd h (by simp)
        rw [h₁, h₂] at h
        obtain rfl : l₁ ++ l₂ = l := Option.some.inj h
        -- the start lies in one half, and that half's segments answer for it
        rw [← Real.Zonotope.split_union R j] at hx
        rcases hx with hx | hx
        · obtain ⟨S, hS, hP⟩ := ih _ _ h₁ x hx
          exact ⟨S, List.mem_append_left _ hS, hP⟩
        · obtain ⟨S, hS, hP⟩ := ih _ _ h₂ x hx
          exact ⟨S, List.mem_append_right _ hS, hP⟩
    · rw [hs] at h
      obtain rfl : [S] = l := Option.some.inj h
      exact ⟨S, List.mem_singleton_self S, hstep R S hs x hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
