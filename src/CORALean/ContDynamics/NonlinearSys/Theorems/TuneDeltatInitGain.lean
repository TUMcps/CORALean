module

public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInit
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# What the first step's search for `Δ` buys

The soundness of lines 3-7 of [1, Alg. 2]: a horizon the search reports meets eq. (32)'s
condition `φ₁ ≥ ζ_Δ`, and it is the initialization of line 2 scaled down by `ζ_δ` a whole number
of times, at least once. It is not a minimum: the horizon reported is the *first* on the grid
`ζ_δ^j Δinit` that clears the condition, hence the largest of them, what §3.4 wants. One
hypothesis, on the caller's check: `le a b = true` implies `a ≤ b`; a check that gives up early
shrinks `Δ` further and never reports a horizon that fails (32). The induction is on the
search's own fuel; nothing here needs it to terminate.

## Inputs
* `le` – comparison of reals
* `dabs` – box diameter of the abstraction error
* `ζδ` – limit gain
* `ζΔ` – gain threshold

## Hypotheses
* `hle` – comparison implies less-or-equal

## Conclusion
* the horizon meets the gain condition and is a scaled initialization

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] lines 3-7: the horizon reported meets eq. (32)'s condition, and
is the initialization scaled by `ζ_δ` a positive number of times. -/
theorem tuneDeltatInit_gain {le : ℝ → ℝ → Bool} (hle : ∀ a b : ℝ, le a b = true → a ≤ b)
    (dabs : ℝ → Fin n → ℝ) (ζδ ζΔ : ℝ) : -- --- CONCL ---
    ∀ (fuel : ℕ) (Δ : ℝ) (p : NonlinearSys.TunedStep ℝ),
      tuneDeltatInit le dabs ζδ ζΔ Δ fuel = some p →
      ζΔ ≤ p.gain ∧ ∃ j : ℕ, p.step = ζδ ^ (j + 1) * Δ := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro Δ p h; rw [tuneDeltatInit] at h; exact absurd h (by simp)
  | succ k ih =>
    intro Δ p h
    simp only [tuneDeltatInit] at h
    split at h
    -- the gain cleared `ζ_Δ`, so this shrinking is the one reported
    · rename_i hc
      rw [Option.some.injEq] at h
      subst h
      exact ⟨hle _ _ hc, 0, by ring⟩
    · obtain ⟨hφ, j, hj⟩ := ih (ζδ * Δ) p h
      exact ⟨hφ, j + 1, by rw [hj]; ring⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
