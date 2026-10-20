module

public import CORALean.NN.Layers.Definitions.PolyOfSampling
public import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtEvalPoly
public import CORALean.NN.Layers.Theorems.Real.SampleBoundsOfDeriv
public import CORALean.Global.Float.Instances.Real.Theorems.Basic

@[expose] public section

/-!
# The exactly sampled polynomial relaxation is sound

ℝ-only, the sampling being exact: a derivative bound on `σ` minus the fit, and a positive
sample count, and `sample_bounds_of_deriv` does the rest; the two ends average into the
constant, so what is left of them is a radius.

## Inputs
* `σ` – activation function
* `σ'` – its derivative
* `n` – polynomial degree
* `c` – fit coefficients for each interval
* `M` – derivative bound for each interval
* `N` – sample count for each interval

## Hypotheses
* `hd` – the activation has the given derivative
* `hM` – derivative differs from the fit's by at most the bound
* `hN` – sample counts are positive

## Conclusion
* the sampled polynomial relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofSampling_sound {σ σ' : ℝ → ℝ} {n : ℕ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (M : ℝ → ℝ → ℝ) (N : ℝ → ℝ → ℕ)
    (hM : ∀ l u x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv (c l u) x| ≤ M l u)
    (hN : ∀ l u, 0 < N l u) : -- --- CONCL ---
    (PolyRelaxation.ofSampling σ c M N).Sound σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  have hg : ∀ x, HasDerivAt (fun y => σ y - evalPoly (c l u) y)
      (σ' x - evalPolyDeriv (c l u) x) x :=
    fun x => (hd x).sub (hasDerivAt_evalPoly (c l u) x)
  obtain ⟨hlow, hhigh⟩ :=
    sample_bounds_of_deriv hg (fun x hx hx' => hM l u x hx hx') (hN l u) hl hu
  -- the two ends average into the constant, so what is left of them is a radius
  show |σ t - evalPoly (fun k => (PolyRelaxation.ofSampling σ c M N).coeffs l u k) t|
    ≤ (PolyRelaxation.ofSampling σ c M N).error l u
  simp only [PolyRelaxation.ofSampling]
  rw [evalPoly_shiftConst, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
