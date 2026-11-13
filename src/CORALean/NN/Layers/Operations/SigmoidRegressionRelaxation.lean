module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.RegressionSlope
public import CORALean.NN.Layers.Operations.SigmoidRelaxation
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The sigmoid relaxation at the regression line

CORA's `nnSigmoidLayer` at `poly_method = 'regression'`, order 1 (the default): the line is the
least-squares line through 20 equally spaced points of the sigmoid on the box. For such points the
slope is a weighted sum, `Σ w_i y_i / (70 (u - l))` with `w_i = 2 i - 19`, computed in floats by
`regressionSlope` and nothing more than a guess. CORA bounds the error of the line by the
extrema `±2 artanh √(1 - 4 m)` of `σ t - m t`; here the slope is clamped into the derivative
bracket and the error is the bracket's (`Relaxation.ofDeriv`), so the quality of the line costs
precision only. The slope-zero relaxation is kept where it is tighter, as for `sigmoidRelaxation`.

## Inputs
* `k` – reduction depth of the exponential

## Output
* relaxation of the sigmoid with the regression slope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The regression slope clamped into the derivative bracket of the box. -/
@[step_of sigmoidRegressionRelaxation]
def step_sigmoidRegressionSlope (E : Enclosure 𝕋) (l u : 𝕋) : 𝕋 :=
  maximum (sigmoidDerivLo E l u) (minimum (sigmoidDerivHi E l u) (regressionSlope E l u))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The derivative-bracket relaxation at the clamped regression slope, or the slope-zero one. -/
def sigmoidRegressionRelaxation (k : ℕ) : Relaxation 𝕋 :=
  Relaxation.tighter
    (Relaxation.ofDeriv (sigmoidEnclosure k) (sigmoidDerivLo (sigmoidEnclosure k))
      (sigmoidDerivHi (sigmoidEnclosure k)) (step_sigmoidRegressionSlope (sigmoidEnclosure k)))
    (Relaxation.ofMonotone (sigmoidEnclosure k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
