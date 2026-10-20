module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# Step `k` of a bounded-horizon run lies inside the horizon

Pure `Set.Icc` arithmetic: a domain covering `[0, KΔt]` covers every step
`[kΔt, (k+1)Δt]` with `k < K`, which is what lets `discretize_horizon` iterate
one step at a time instead of asking for all of forward time.

## Inputs
* `T` – time domain
* `Δt` – step length
* `K` – number of steps
* `k` – step index

## Hypotheses
* `hΔt` – step length nonnegative
* `hT` – time domain contains the horizon
* `hk` – step index below the number of steps

## Conclusion
* the step lies in the time domain
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `k` of a run of `K` steps lies inside the horizon. -/
theorem step_subset_horizon {T : Set ℝ} {Δt : ℝ} {K k : ℕ} (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hk : k < K) :
    Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T := by
  refine fun s hs => hT ⟨le_trans (mul_nonneg (Nat.cast_nonneg k) hΔt) hs.1, ?_⟩
  refine le_trans hs.2 (mul_le_mul_of_nonneg_right ?_ hΔt)
  exact_mod_cast Nat.succ_le_of_lt hk

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
