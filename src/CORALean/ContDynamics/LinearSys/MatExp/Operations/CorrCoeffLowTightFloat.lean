module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Log

@[expose] public section

/-!
# `MatExp.corrCoeffLowTight`, CORA's correction coefficient bounded from below

`Real.MatExp.corrCoeff i = a^i − a` at `a = i^(−1/(i−1))`, which CORA computes with MATLAB's
`power` (no float guarantee). Since `a^(i−1) = 1/i`, the coefficient is `−(1 − 1/i)·a`, and
`a = exp(−log i / (i − 1))`: here `log i` is rounded down, the quotient down, the exponential up,
the product up, so the result is below the coefficient and at `nearest` within rounding of
CORA's. `corrCoeffLow`'s Bernoulli bound `−(1 − 1/i)²` is `15%` lower at `i = 3`. Past the
order `1024` the logarithm's range is left and `corrCoeffLow` is taken.

## Inputs
* `i` – order

## Output
* float lower bound of the correction coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A float lower bound of `corrCoeff i`, `−(1 − 1/i) · i^(−1/(i−1))` rounded outward. -/
def MatExp.corrCoeffLowTight (i : ℕ) : 𝕋 :=
  if 2 ≤ i ∧ i ≤ 1024 then
    let d := maximum one (nsmulDown i one)                             -- `i`, at least `1`
    let q := divUp (nsmulUp (i - 1) one) d                             -- `q ≥ (i − 1)/i`
    let ℓ := logDown 16 64 d                                           -- `ℓ ≤ log i`
    let x := minimum zero (neg (divDown ℓ (nsmulUp (i - 1) one)))      -- `x ≥ −log i/(i − 1)`
    neg (mulUp q (expUp 16 x))                                         -- `−q · e^x`
  else MatExp.corrCoeffLow i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
