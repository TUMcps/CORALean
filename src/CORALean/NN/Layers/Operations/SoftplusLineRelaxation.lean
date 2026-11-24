module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.NN.Layers.Operations.RegressionSlope
public import CORALean.NN.Layers.Operations.OnePlusExpDown
public import CORALean.Global.Float.LogDownPos
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The line of softplus

CORA.cpp's `priv_monotone_line` for softplus `f(x) = log(1 + e^x)`, with the lower end from the
closed-form minimum. The slope `m` is Singh's `f'(l) = 1 / (e^(-l) + 1)` or the least-squares slope
through twenty points (`regressionSlope`). `g(x) = f(x) - m x` is convex, so on the box it is at
most the larger of `g(l)` and `g(u)`. For `0 < m < 1` it is at least its minimum over the line,
`-(m log m) - (1 - m) log(1 - m)` at `x = log(m / (1 - m))`, for `m ≤ 0` or `1 ≤ m` the smaller end
value; a sound format that decides neither takes the smaller of `-m l` and `-m u`, below `g` as
`f > 0`. The band goes to `Relaxation.ofBand` without a margin; at round to nearest this is
CORA.cpp's order.

## Inputs
* `regression` – the least-squares slope (CORA's default), else Singh's
* `k` – the exponential's reduction depth
* `p` – the logarithm's bisection steps

## Output
* the line of softplus
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `log(1 + e^x)` from below and above. -/
@[step_of softplusLineRelaxation]
def step_softplusLineEnclosure (k p : ℕ) : Enclosure 𝕋 where
  enclose x := ⟨logDownPos k p (onePlusExpDown k x), logUp k p (addUp one (expUp k x))⟩

/-- The least-squares slope, or Singh's `1 / (e^(-l) + 1)`. -/
@[step_of softplusLineRelaxation]
def step_softplusLineSlope (regression : Bool) (k p : ℕ) (l u : 𝕋) : 𝕋 :=
  if regression then regressionSlope (step_softplusLineEnclosure k p) l u
  else divDown one (addDown (expDown k (neg l)) one)

/-- The smaller of `g(l)` and `g(u)`, and the closed-form minimum where `0 < m < 1`, rounded
down. -/
@[step_of softplusLineRelaxation]
def step_softplusLineLo (regression : Bool) (k p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_softplusLineSlope regression k p l u
  let g := fun x => subDown ((step_softplusLineEnclosure k p).enclose x).inf (mulUp m x)
  let ends := minimum (g l) (g u)
  if ltStrict zero m && ltStrict m one then
    let t := subDown one m                                             -- 1 - m, both ways
    let tU := subUp one m
    let L := logUp k p tU                                              -- log(1 - m)
    minimum ends (subDown (neg (mulUp m (logUp k p m))) (maximum (mulUp t L) (mulUp tU L)))
  else if le m zero || le one m then ends
  else minimum (neg (mulUp m l)) (neg (mulUp m u))

/-- The larger of `g(l)` and `g(u)`, rounded up. -/
@[step_of softplusLineRelaxation]
def step_softplusLineHi (regression : Bool) (k p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_softplusLineSlope regression k p l u
  let g := fun x => subUp ((step_softplusLineEnclosure k p).enclose x).sup (mulDown m x)
  maximum (g l) (g u)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `log(1 + e^x) - m x`, its middle and half its width. -/
def softplusLineRelaxation (regression : Bool) (k p : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofBand (step_softplusLineSlope regression k p) (step_softplusLineLo regression k p)
    (step_softplusLineHi regression k p) fun _ _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
