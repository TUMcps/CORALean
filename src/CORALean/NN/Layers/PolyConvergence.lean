import CORALean.NN.Layers.PolySampling

/-!
# Refinement by sampling converges

`PolyRelaxation.ofSampling` pays twice: half the sampled range of `g = σ - p`,
and a padding `M · (u - l) / N` the mean value theorem asks for between two
samples. Only the first is real. As the sample count grows the padding vanishes
and the error tends to `boxHalfRange g l u`, half the range `g` actually spans
over the box — what these coefficients cost, and what no bound can beat.

That is what makes spending samples on a neuron worth doing. A bound that only
over-approximates says nothing about whether refining it helps; this says the
error does not stall above the true half-range, so the effort is never spent
against a floor that is an artefact of `minMaxDiffOrder` [1] rather than of `p`.

`samplingError_bracket` is the finite statement behind the limit, and the more
useful one at a fixed `N`: the error is never below the half-range — soundness
once more — and never more than one padding above it, so the padding is not
merely asymptotically negligible, it is the whole gap.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- What `ofSampling` charges for `g` over `[l, u]` at `N` samples, read as a
function of `N` so that a limit in it can be stated. -/
noncomputable def samplingError (g : ℝ → ℝ) (M l u : ℝ) (N : ℕ) : ℝ :=
  (sampleSup g l u N - sampleInf g l u N) / 2 + M * ((u - l) / N)

/-- Half the range `g` spans over the box: the error a recentred fit of these
coefficients leaves, with no sampling in it. -/
noncomputable def boxHalfRange (g : ℝ → ℝ) (l u : ℝ) : ℝ :=
  (sSup (g '' Set.Icc l u) - sInf (g '' Set.Icc l u)) / 2

/-- The construction's error is `samplingError` at the fit's residual, which is
what ties the limit below to `ofSampling` rather than to a lookalike. -/
theorem PolyRelaxation.ofSampling_error {σ σ' : ℝ → ℝ} {n : ℕ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (M : ℝ → ℝ → ℝ) (N : ℝ → ℝ → ℕ)
    (hM : ∀ l u x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv (c l u) x| ≤ M l u)
    (hN : ∀ l u, 0 < N l u) (l u : ℝ) :
    (PolyRelaxation.ofSampling hd c M N hM hN).error l u
      = samplingError (fun x => σ x - evalPoly (c l u) x) (M l u) l u (N l u) := rfl

/-- The sampled error sits above the true half-range and within one padding of
it, so the padding is the entire price of sampling rather than searching. -/
theorem samplingError_bracket {g g' : ℝ → ℝ} {M l u : ℝ} {N : ℕ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hN : 0 < N) (hlu : l ≤ u) :
    boxHalfRange g l u ≤ samplingError g M l u N ∧
      samplingError g M l u N ≤ boxHalfRange g l u + M * ((u - l) / N) := by
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

/-- At fixed coefficients the sampling padding vanishes: the error converges to
the half-range of `g`, so samples are never spent against an artificial floor. -/
theorem tendsto_samplingError {g g' : ℝ → ℝ} {M l u : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hlu : l ≤ u) :
    Filter.Tendsto (fun N : ℕ => samplingError g M l u N) Filter.atTop
      (nhds (boxHalfRange g l u)) := by
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
