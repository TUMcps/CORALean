module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.NN.Layers.Operations.RegressionSlope
public import CORALean.Global.Float.SqrtDownCora
public import CORALean.Global.Float.LogDownPos
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The line of the inverse square root

CORA.cpp's `priv_monotone_line` for `f(x) = 1 / √x`, computed as `√(1 / x)`, on boxes with
`0 < l`, with the lower end from the closed-form minimum. The slope `m` is Singh's
`f'(u) = -(1 / √(u u u)) / 2` or the least-squares slope through twenty points
(`regressionSlope`). `g(x) = 1 / √x - m x` is convex, so on the box it is at most the larger of
`g(l)` and `g(u)`. For `m < 0` it is at least its minimum over the half-line, `(3 / 2) c` with
`c = (-2 m)^(1/3) = exp(log(-m - m) / 3)`; for `0 ≤ m` the smaller end value. A sound format
deciding neither takes `min(-m l, -m u)`, one with `-m - m` or `3` not positive takes `0`. The band
goes to `Relaxation.ofBand` without a margin; at round to nearest this is CORA.cpp's order.

## Inputs
* `regression` – the least-squares slope (CORA's default), else Singh's
* `k` – the exponential's reduction depth
* `p` – the square root's Newton steps and the logarithm's bisection steps

## Output
* the line of the inverse square root
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

/-- `√(1 / x)` from below and above. -/
@[step_of invSqrtRootLineRelaxation]
def step_invSqrtRootLineEnclosure (p : ℕ) : Enclosure 𝕋 where
  enclose x := ⟨sqrtDownCora p (divDown one x), sqrtUp p (divUp one x)⟩

/-- The least-squares slope, or Singh's `-(1 / √(u u u)) / 2`. -/
@[step_of invSqrtRootLineRelaxation]
def step_invSqrtRootLineSlope (regression : Bool) (p : ℕ) (l u : 𝕋) : 𝕋 :=
  if regression then regressionSlope (step_invSqrtRootLineEnclosure p) l u
  else half (neg (divDown one (sqrtDownCora p (mulDown (mulDown u u) u))))

/-- The smaller of `g(l)` and `g(u)`, and the closed-form minimum `(3 / 2) (-2 m)^(1/3)` where
`m < 0`, rounded down. -/
@[step_of invSqrtRootLineRelaxation]
def step_invSqrtRootLineLo (regression : Bool) (k p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_invSqrtRootLineSlope regression p l u
  let g := fun x => subDown ((step_invSqrtRootLineEnclosure p).enclose x).inf (mulUp m x)
  let ends := minimum (g l) (g u)
  if ltStrict m zero then
    let y := addDown (neg m) (neg m)                                   -- -2 m
    let three := nsmulDown 3 one
    if ltStrict zero y && ltStrict zero three then
      let L := logDownPos k p y                                        -- log(-2 m)
      let c := expDown k (minimum (divDown L three) (divDown L (nsmulUp 3 one)))  -- (-2 m)^(1/3)
      minimum ends (addDown c (half c))
    else minimum ends zero
  else if le zero m then ends
  else minimum (neg (mulUp m l)) (neg (mulUp m u))

/-- The larger of `g(l)` and `g(u)`, rounded up. -/
@[step_of invSqrtRootLineRelaxation]
def step_invSqrtRootLineHi (regression : Bool) (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_invSqrtRootLineSlope regression p l u
  let g := fun x => subUp ((step_invSqrtRootLineEnclosure p).enclose x).sup (mulDown m x)
  maximum (g l) (g u)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `1 / √x - m x`, its middle and half its width. -/
def invSqrtRootLineRelaxation (regression : Bool) (k p : ℕ) : Relaxation 𝕋 :=
  Relaxation.ofBand (step_invSqrtRootLineSlope regression p) (step_invSqrtRootLineLo regression k p)
    (step_invSqrtRootLineHi regression p) fun _ _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
