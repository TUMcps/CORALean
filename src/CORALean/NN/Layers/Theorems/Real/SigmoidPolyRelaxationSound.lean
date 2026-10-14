module

public import CORALean.NN.Layers.Definitions.SigmoidPoly
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.Real.AbsSubEvalPolyDerivLe
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.OfSamplingSound
public import CORALean.NN.Layers.Theorems.Real.SigmoidDerivLoLe

@[expose] public section

/-!
# The exact polynomial sigmoid relaxation is sound

ℝ-only, the sampling and the bracket being exact: the sigmoid's bracket bounds `σ'`, so the two
brackets subtracted bound what `ofSampling` asks about.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidPolyRelaxation_sound {n : ℕ} (c : ℝ → ℝ → Fin (n + 1) → ℝ) (N : ℝ → ℝ → ℕ)
    (hN : ∀ l u, 0 < N l u) : (sigmoidPolyRelaxation c N).Sound sigmoid :=
  PolyRelaxation.ofSampling_sound hasDerivAt_sigmoid c _ N
    (fun _ _ _ hx hx' => abs_sub_evalPolyDeriv_le (sigmoidDerivLo_le hx hx')
      (le_sigmoidDerivHi hx hx') hx hx') hN

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
