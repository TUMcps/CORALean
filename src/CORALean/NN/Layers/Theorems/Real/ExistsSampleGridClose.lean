module

public import CORALean.NN.Layers.Definitions.PolySampling

@[expose] public section

/-!
# Every point of the box is near an exact sample

ℝ-only, as the grid is: within one spacing, the sample below the point named by the floor.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box
* `t` – point in the box
* `N` – number of sample intervals

## Hypotheses
* `hN` – number of intervals is positive
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* some sample lies within one grid step of the point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_sampleGrid_close {l u t : ℝ} {N : ℕ} (hN : 0 < N) (hl : l ≤ t) (hu : t ≤ u) :
    ∃ i : Fin (N + 1), |t - sampleGrid l u N i| ≤ (u - l) / N := by -- --- PROOF ---
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfull : (N : ℝ) * ((u - l) / N) = u - l := by
    field_simp
  rcases eq_or_lt_of_le (hl.trans hu) with hlu | hlu
  · -- a degenerate box: the spacing is zero and the left end is the only point
    refine ⟨0, ?_⟩
    have ht : t = l := le_antisymm (by rw [hlu]; exact hu) hl
    have hdx : (u - l) / N = 0 := by rw [← hlu, sub_self, zero_div]
    have hg : sampleGrid l u N (0 : Fin (N + 1)) = l := by
      show l + ((0 : Fin (N + 1)) : ℕ) * ((u - l) / N) = l
      rw [hdx, mul_zero, add_zero]
    rw [ht, hg, sub_self, abs_zero, hdx]
  · have hdxpos : 0 < (u - l) / N := div_pos (by linarith) hNpos
    have hq : 0 ≤ (t - l) / ((u - l) / N) := div_nonneg (by linarith) hdxpos.le
    have hqN : (t - l) / ((u - l) / N) ≤ (N : ℝ) := by
      rw [div_le_iff₀ hdxpos, hfull]
      linarith
    -- the sample below `t`, which the floor names and the box's width keeps in range
    have hkN : ⌊(t - l) / ((u - l) / N)⌋₊ ≤ N := by
      have hfloor := Nat.floor_le_floor hqN
      rwa [Nat.floor_natCast] at hfloor
    refine ⟨⟨⌊(t - l) / ((u - l) / N)⌋₊, by omega⟩, ?_⟩
    have hfl : ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) ≤ (t - l) / ((u - l) / N) :=
      Nat.floor_le hq
    have hfu : (t - l) / ((u - l) / N) < (⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) + 1 :=
      Nat.lt_floor_add_one _
    rw [le_div_iff₀ hdxpos] at hfl
    rw [div_lt_iff₀ hdxpos] at hfu
    have hexp : (((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) + 1) * ((u - l) / N)
        = ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) * ((u - l) / N) + (u - l) / N := by
      ring
    show |t - (l + ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) * ((u - l) / N))| ≤ (u - l) / N
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
