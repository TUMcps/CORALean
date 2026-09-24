import CORALean.NN.Layers.Definitions.PolyOfSampling

/-!
# The sampled relaxation's error is the sampling error

ℝ-only, as the construction is: by `rfl`, which ties the convergence theorems to `ofSampling`
rather than to a lookalike.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofSampling_error {n : ℕ} (σ : ℝ → ℝ) (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (M : ℝ → ℝ → ℝ) (N : ℝ → ℝ → ℕ) (l u : ℝ) :
    (PolyRelaxation.ofSampling σ c M N).error l u
      = samplingError (fun x => σ x - evalPoly (c l u) x) (M l u) l u (N l u) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
