module

public import CORALean.NN.Layers.Operations.PolyDerivBoundUp
public import CORALean.NN.Layers.Operations.PolyRelaxationOfSampling
public import CORALean.NN.Layers.Operations.SigmoidDerivHi
public import CORALean.NN.Layers.Operations.SigmoidDerivLo
public import CORALean.NN.Layers.Operations.SigmoidEnclosure
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The polynomial relaxation at the sigmoid

`ofSampling` at the sigmoid: `sigmoidEnclosure` is `σ` at a stored value, the derivative bracket
turns into the `M` the sampling bound asks for, and the fit `c` and grid `p`, `dx` stay free —
any array of stored values is a fit, and a grid that fails its check costs precision only.

## Inputs
* `k` – reduction depth of the exponential
* `c` – fit coefficients for each box
* `dx` – grid spacing for each box
* `p` – proposed sample grid for each box

## Output
* polynomial relaxation of the sigmoid from the fit and its checked grid
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {N : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `Sigmoid`'s derivative bracket read against the fit's own. -/
@[step_of sigmoidPolyRelaxation]
def step_sigmoidPolyDerivBound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  polyDerivBoundUp (c l u) (sigmoidDerivLo (sigmoidEnclosure k) l u)
    (sigmoidDerivHi (sigmoidEnclosure k) l u) l u


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ofSampling` at the sigmoid, the fit and the grid free. -/
def sigmoidPolyRelaxation (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofSampling (sigmoidEnclosure k) c (step_sigmoidPolyDerivBound k c) dx p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
