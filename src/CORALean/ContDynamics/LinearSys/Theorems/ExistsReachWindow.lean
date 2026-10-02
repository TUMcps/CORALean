import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.Algebra.CharP.Defs

/-!
# Every time of the horizon falls in a window `reach` keeps

`reachWrappingFree` covers `[0, tFinal]` with `max 1 ⌈tFinal / Δt⌉₊` windows
`[k Δt, (k + 1) Δt]`; a time `t` of the horizon is in the one with
`k = ⌈t / Δt⌉ - 1`, the window whose right end is the first to reach `t`, and
`t = 0` in the first. Stated once for `LinearSys.reachWrappingFree` and
`LinearSys.WithInput.reach` alike, the two counting their windows the same way;
`LinearSys.reach` keeps `⌈tFinal / Δt⌉₊`, the same count once `0 < tFinal`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `t ∈ [0, tFinal]` is in a window `[k Δt, k Δt + Δt]` that `reach` keeps. -/
theorem LinearSys.exists_reach_window {tFinal Δt t : ℝ} (hΔt : 0 < Δt)
    (ht : t ∈ Set.Icc 0 tFinal) :
    ∃ k < max 1 ⌈tFinal / Δt⌉₊, (k : ℝ) * Δt ≤ t ∧ t - k * Δt ≤ Δt := by -- --- PROOF ---
  -- `k = c - 1`, the window whose right end `c Δt` is the first to reach `t`
  obtain ⟨c, hc⟩ : ∃ c, c = ⌈t / Δt⌉₊ := ⟨_, rfl⟩
  have hq : 0 ≤ t / Δt := div_nonneg ht.1 hΔt.le
  have hcN : c ≤ ⌈tFinal / Δt⌉₊ := hc ▸ Nat.ceil_mono (div_le_div_of_nonneg_right ht.2 hΔt.le)
  have hup : t ≤ c * Δt := (div_le_iff₀ hΔt).mp (hc ▸ Nat.le_ceil _)
  refine ⟨c - 1, by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · simp [h0, ht.1]
    · have hlt : (c : ℝ) < t / Δt + 1 := hc ▸ Nat.ceil_lt_add_one hq
      rw [Nat.cast_sub hpos, Nat.cast_one, ← le_div_iff₀ hΔt]
      linarith
  · have hc1 : (c : ℝ) ≤ ((c - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : c ≤ c - 1 + 1)
    nlinarith [mul_le_mul_of_nonneg_right hc1 hΔt.le]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
