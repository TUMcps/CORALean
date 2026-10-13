import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A step starting in forward time stays there

Every step of a nonnegative length sits in forward time, so a domain covering
`[0, ∞)` covers each of them. Needed by both `discretize` and
`discretize_inputSolution`, so it is stated once here rather than duplicated
into each — the two ask for the same step, over a total run and one bounded by
`inputSolution` respectively.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem step_subset {T : Set ℝ} {Δt : ℝ} (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T) (k : ℕ) :
    Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T :=
  fun _ hs => hT (le_trans (mul_nonneg (Nat.cast_nonneg k) hΔt) hs.1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
