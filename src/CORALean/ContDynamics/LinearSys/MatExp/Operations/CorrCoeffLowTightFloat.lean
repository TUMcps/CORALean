module

public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Log
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.corrCoeffLowTight`, CORA's correction coefficient bounded from below

`Real.MatExp.corrCoeff i = a^i − a` at `a = i^(−1/(i−1))`, which CORA computes with MATLAB's
`power` (no float guarantee). Since `a^(i−1) = 1/i`, the coefficient is `−(1 − 1/i)·a`, and
`a = exp(−log i / (i − 1))`: here `log i` is rounded down, the quotient down, the exponential up,
the product up, so the result is below the coefficient and at `nearest` within rounding of
CORA's. `step_corrCoeffLow`'s Bernoulli bound `−(1 − 1/i)²` is `15%` lower at `i = 3`, but exact at
`i = 2`, where the rounded logarithm costs the tight value `3%` at 24 bits; the larger of the two
lower bounds is taken. Past the order `1024` the logarithm's range is left and `step_corrCoeffLow`
is taken.

## Inputs
* `i` – order

## Output
* float lower bound of the correction coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   18-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `-(1 - 1/i)²`, rounded down: `(i - 1)/i` over a denominator held between `1` and `i`, squared
upwards, then negated exactly (Bernoulli's inequality puts `a` below `1 - 1/i`). -/
@[step_of MatExp.corrCoeffLowTight]
def MatExp.step_corrCoeffLow (i : ℕ) : 𝕋 :=
  let q := divUp (nsmulUp (i - 1) one) (maximum one (nsmulDown i one))  -- q ≥ (i - 1)/i
  neg (mulUp q q)                                                       -- -q² ≤ -(1 - 1/i)²


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A float lower bound of `corrCoeff i`, `−(1 − 1/i) · i^(−1/(i−1))` rounded outward, or the
Bernoulli bound where that is larger. -/
def MatExp.corrCoeffLowTight (i : ℕ) : 𝕋 :=
  if 2 ≤ i ∧ i ≤ 1024 then
    let d := maximum one (nsmulDown i one)                             -- `i`, at least `1`
    let q := divUp (nsmulUp (i - 1) one) d                             -- `q ≥ (i − 1)/i`
    let ℓ := logDown 16 64 d                                           -- `ℓ ≤ log i`
    let x := minimum zero (neg (divDown ℓ (nsmulUp (i - 1) one)))      -- `x ≥ −log i/(i − 1)`
    maximum (MatExp.step_corrCoeffLow i) (neg (mulUp q (expUp 16 x)))  -- the better bound
  else MatExp.step_corrCoeffLow i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
