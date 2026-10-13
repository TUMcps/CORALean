import CORALean.NN.Layers.Theorems.Real.SamplingErrorBracket

/-!
# Refinement by sampling converges

ℝ-only, as the sampled range is: at fixed coefficients the padding vanishes and the error
converges to the half-range of `g`, so samples are never spent against an artificial floor —
one that is an artefact of `minMaxDiffOrder` [1] rather than of the fit.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem tendsto_samplingError {g g' : ℝ → ℝ} {M l u : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hlu : l ≤ u) :
    Filter.Tendsto (fun N : ℕ => samplingError g M l u N) Filter.atTop
      (nhds (boxHalfRange g l u)) := by -- --- PROOF ---
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM l le_rfl hlu)
  have hpad : Filter.Tendsto (fun N : ℕ => M * ((u - l) / N)) Filter.atTop (nhds 0) := by
    have heq : (fun N : ℕ => M * ((u - l) / N)) = fun N : ℕ => (M * (u - l)) / N := by
      funext N
      ring
    rw [heq]
    exact tendsto_const_div_atTop_nhds_zero_nat (M * (u - l))
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hpad
  -- a degenerate sample count is left behind, and past it the bracket is the bound
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  obtain ⟨hlow, hhigh⟩ := samplingError_bracket hd hM hN hlu
  have hdx : 0 ≤ M * ((u - l) / N) :=
    mul_nonneg hM0 (div_nonneg (by linarith) (Nat.cast_nonneg N))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
