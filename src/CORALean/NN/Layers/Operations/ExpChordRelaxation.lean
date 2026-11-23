module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Log
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The chord relaxation of the exponential

CORA.cpp's `priv_exp_line`, with the lower end from the closed-form minimum. The slope `m` is the
chord's on `[l, u]` (`e^l` on a point, the width kept above `τ`), clamped at zero.
`g(x) = e^x - m x` is convex, so on the box it is at most the larger of `g(l)` and `g(u)`; for
`m > 0` it is at least its minimum over the line, `m - m log m` at `x = log m`; for `m = 0`,
`g(l)`. A sound format that decides neither sign takes `-m u`, below `g` as `e^x > 0`. The
band goes to `Relaxation.ofBand` with CORA.cpp's margin `w (e^u + m max(|l|, |u|))`; at round to
nearest this is CORA.cpp's order.

## Inputs
* `k` – the exponential's reduction depth
* `p` – the logarithm's bisection steps
* `τ` – the least width the chord divides by (CORA.cpp's `kTiny`)
* `w` – the margin's factor (CORA.cpp's `16 eps`)

## Output
* the chord relaxation of the exponential
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

/-- The chord's slope on `[l, u]`, `e^l` on a point, clamped at zero. -/
@[step_of expChordRelaxation]
def step_expChordSlope (k : ℕ) (τ l u : 𝕋) : 𝕋 :=
  let el := expDown k l
  let eu := expUp k u
  let width := subUp u l
  let chord := if ltStrict zero width then divUp (subUp eu el) (maximum width τ) else el
  maximum chord zero

/-- The larger of `g(l)` and `g(u)`, `g(x) = e^x - m x`, rounded up. -/
@[step_of expChordRelaxation]
def step_expChordHi (k : ℕ) (τ l u : 𝕋) : 𝕋 :=
  let m := step_expChordSlope k τ l u
  maximum (subUp (expUp k l) (mulDown m l)) (subUp (expUp k u) (mulDown m u))

/-- `m - m log m` for `m > 0`, `g(l)` for `m = 0`, rounded down. -/
@[step_of expChordRelaxation]
def step_expChordLo (k p : ℕ) (τ l u : 𝕋) : 𝕋 :=
  let m := step_expChordSlope k τ l u
  if ltStrict zero m then subDown m (mulUp m (logUp k p m))
  else if le m zero then subDown (expDown k l) (mulUp m l)
  else neg (mulUp m u)

/-- CORA.cpp's margin `w (e^u + m max(|l|, |u|))`, rounded up. -/
@[step_of expChordRelaxation]
def step_expChordMargin (k : ℕ) (τ w l u : 𝕋) : 𝕋 :=
  let m := step_expChordSlope k τ l u
  mulUp (addUp (expUp k u) (mulUp m (maximum (absolute l) (absolute u)))) w


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `e^x - m x` at the chord's slope, its middle and half its width plus the margin. -/
def expChordRelaxation (k p : ℕ) (τ w : 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofBand (step_expChordSlope k τ) (step_expChordLo k p τ) (step_expChordHi k τ)
    (step_expChordMargin k τ w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
