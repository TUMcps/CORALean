import CORALean.NN.Layers.Definitions.PolyAffineConj
import CORALean.NN.Layers.Definitions.PolyDerivBound
import CORALean.NN.Layers.Definitions.PolyFit
import CORALean.NN.Layers.Definitions.PolyOfSampling
import CORALean.NN.Layers.Definitions.SigmoidRelaxation

/-!
# The polynomial relaxations at the sigmoid and at tanh, over ℝ

`ofSampling` at the sigmoid, exactly: `M` is the sigmoid's exact derivative bracket against the
fit's own, the coefficients `c` and the sample count `N` free — any fit is sound once the bound
holds, and any positive count is — and `polyFit` is one choice, CORA's default. Tanh follows at
every order by `tanh t = 2 σ (2 t) - 1`: `ofAffineConj` rescales the coefficients and the error.
Nothing is given away against `Relaxation.ofDeriv` at order 1: `polyDerivDiff_one` says the
derivative bound is there exactly its bracket. Specifications over ℝ; the runnable relaxation is
`sigmoidPolyRelaxation`, at a stored enclosure and a checked grid.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ofSampling` at the sigmoid, the fit `c` and the sample count `N` free. -/
noncomputable def sigmoidPolyRelaxation (c : ℝ → ℝ → Fin (n + 1) → ℝ) (N : ℝ → ℝ → ℕ) :
    CORALean.PolyRelaxation ℝ n :=
  PolyRelaxation.ofSampling sigmoid c
    (fun l u => polyDerivDiff (sigmoidDerivLo l u) (sigmoidDerivHi l u)
      (polyDerivCenter (c l u)) (polyDerivRadius (c l u) l u)) N

/-- The same at CORA's default fit, which leaves only the sample count to choose. -/
noncomputable def sigmoidPolyRelaxationFit (N : ℝ → ℝ → ℕ) : CORALean.PolyRelaxation ℝ n :=
  sigmoidPolyRelaxation (polyFit sigmoid n) N

/-- `sigmoidPolyRelaxation` read through `tanh t = 2 σ (2 t) - 1`: `a = b = 2`, `d = -1`. -/
noncomputable def tanhPolyRelaxation (c : ℝ → ℝ → Fin (n + 1) → ℝ) (N : ℝ → ℝ → ℕ) :
    CORALean.PolyRelaxation ℝ n :=
  PolyRelaxation.ofAffineConj (sigmoidPolyRelaxation c N) 2 2 (-1)

/-- The same at CORA's default fit of the sigmoid, conjugated. -/
noncomputable def tanhPolyRelaxationFit (N : ℝ → ℝ → ℕ) : CORALean.PolyRelaxation ℝ n :=
  tanhPolyRelaxation (polyFit sigmoid n) N

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
