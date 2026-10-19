module

public import CORALean.NN.Layers.Theorems.Real.SampleBoundsOfDeriv

@[expose] public section

/-!
# Sampling costs one padding over the true half-range

ℝ-only, as the sampled range is: above the true half-range — soundness once more — and within
one padding of it, so the padding is the entire price of sampling rather than searching.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem samplingError_bracket {g g' : ℝ → ℝ} {M l u : ℝ} {N : ℕ}
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
