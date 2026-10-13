import CORALean.NN.Layers.Definitions.PolySampling

/-!
# The exact sample grid lies in the box

ℝ-only, the grid being exact: the last index is `N`, so no sample steps past the right end.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sampleGrid_mem_Icc {l u : ℝ} {N : ℕ} (hN : 0 < N) (hlu : l ≤ u) (i : Fin (N + 1)) :
    l ≤ sampleGrid l u N i ∧ sampleGrid l u N i ≤ u := by -- --- PROOF ---
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdx : 0 ≤ (u - l) / N := div_nonneg (by linarith) hNpos.le
  have hfull : (N : ℝ) * ((u - l) / N) = u - l := by
    field_simp
  -- the last index is `N`, so no sample steps past the right end
  have hstep : ((i : ℕ) : ℝ) * ((u - l) / N) ≤ (N : ℝ) * ((u - l) / N) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.isLt)) hdx
  have hlow : 0 ≤ ((i : ℕ) : ℝ) * ((u - l) / N) := mul_nonneg (Nat.cast_nonneg _) hdx
  exact ⟨by simp only [sampleGrid]; linarith, by simp only [sampleGrid]; linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
