module

public import CORALean.NN.Layers.Theorems.Real.SampleBoundsOfDeriv

@[expose] public section

/-!
# Refinement by sampling converges

ℝ-only, as the sampled range is: at fixed coefficients the padding vanishes and the error
converges to the half-range of `g`, so samples are never spent against an artificial floor —
one that is an artefact of `minMaxDiffOrder` [1] rather than of the fit.

## Inputs
* `g` – function
* `g'` – its derivative
* `M` – bound on the derivative
* `l` – lower end of the box
* `u` – upper end of the box

## Hypotheses
* `hd` – the function has the given derivative
* `hM` – derivative is bounded on the box
* `hlu` – box is ordered

## Conclusion
* the sampling error converges to the half-range as the sample count grows

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Sampling costs one padding over the true half-range. -/
private theorem aux_samplingError_bracket {g g' : ℝ → ℝ} {M l u : ℝ} {N : ℕ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hN : 0 < N) (hlu : l ≤ u) : -- --- CONCL ---
    boxHalfRange g l u ≤ samplingError g M l u N ∧
      samplingError g M l u N ≤ boxHalfRange g l u + M * ((u - l) / N) := by -- --- PROOF ---
  have hne : (g '' Set.Icc l u).Nonempty := ⟨g l, ⟨l, ⟨le_rfl, hlu⟩, rfl⟩⟩
  have hmem : ∀ i : Fin (N + 1), sampleGrid l u N i ∈ Set.Icc l u := fun i =>
    ⟨(sampleGrid_mem_Icc hN hlu i).1, (sampleGrid_mem_Icc hN hlu i).2⟩
  -- the padded sampled range is itself a bound on the image, so no compactness is needed
  have hbA : BddAbove (g '' Set.Icc l u) := by
    refine ⟨sampleSup g l u N + M * ((u - l) / N), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (sample_bounds_of_deriv hd hM hN hx.1 hx.2).2
  have hbB : BddBelow (g '' Set.Icc l u) := by
    refine ⟨sampleInf g l u N - M * ((u - l) / N), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (sample_bounds_of_deriv hd hM hN hx.1 hx.2).1
  -- every sample is a point of the box, which puts the sampled range inside the true one
  have h1 : sampleSup g l u N ≤ sSup (g '' Set.Icc l u) :=
    Finset.sup'_le _ _ fun i _ => le_csSup hbA ⟨sampleGrid l u N i, hmem i, rfl⟩
  have h2 : sSup (g '' Set.Icc l u) ≤ sampleSup g l u N + M * ((u - l) / N) := by
    refine csSup_le hne ?_
    rintro y ⟨x, hx, rfl⟩
    exact (sample_bounds_of_deriv hd hM hN hx.1 hx.2).2
  have h3 : sInf (g '' Set.Icc l u) ≤ sampleInf g l u N :=
    Finset.le_inf' _ _ fun i _ => csInf_le hbB ⟨sampleGrid l u N i, hmem i, rfl⟩
  have h4 : sampleInf g l u N - M * ((u - l) / N) ≤ sInf (g '' Set.Icc l u) := by
    refine le_csInf hne ?_
    rintro y ⟨x, hx, rfl⟩
    exact (sample_bounds_of_deriv hd hM hN hx.1 hx.2).1
  show (sSup (g '' Set.Icc l u) - sInf (g '' Set.Icc l u)) / 2
      ≤ (sampleSup g l u N - sampleInf g l u N) / 2 + M * ((u - l) / N)
    ∧ (sampleSup g l u N - sampleInf g l u N) / 2 + M * ((u - l) / N)
      ≤ (sSup (g '' Set.Icc l u) - sInf (g '' Set.Icc l u)) / 2 + M * ((u - l) / N)
  exact ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem tendsto_samplingError {g g' : ℝ → ℝ} {M l u : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hlu : l ≤ u) : -- --- CONCL ---
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
  obtain ⟨hlow, hhigh⟩ := aux_samplingError_bracket hd hM hN hlu
  have hdx : 0 ≤ M * ((u - l) / N) :=
    mul_nonneg hM0 (div_nonneg (by linarith) (Nat.cast_nonneg N))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
