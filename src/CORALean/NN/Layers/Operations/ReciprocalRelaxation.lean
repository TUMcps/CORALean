module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.Global.Float.SqrtDownCora
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The chord relaxation of the clamped reciprocal

CORA.cpp's `priv_reciprocal_line` for `f(x) = 1 / max(x, 1)`, with the lower end from the
closed-form minimum. The slope `m = -1 / (l' u')` is the chord's on `[l', u'] = [max(l, 1),
max(u, 1)]`. `g(x) = f(x) - m x` rises to `x = 1` and is convex after it, so on the box it is at
most the largest of `g(l)`, `g(u)` and `g` at `1` clamped into the box; it is at least the smaller
of `g(l)` (where it rises) and `2 √(-m)`, the least `1/x - m x` takes for `x > 0`. The band goes
to `Relaxation.ofBand` with CORA.cpp's margin `w (1 + |m| max(|l|, |u|))`; at round to nearest
this is CORA.cpp's order.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor (CORA.cpp's `16 eps`)

## Output
* the chord relaxation of the clamped reciprocal
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

/-- The chord's slope `-1 / (l' u')` on `[max(l, 1), max(u, 1)]`, each quotient rounded up. -/
@[step_of reciprocalRelaxation]
def step_reciprocalSlope (l u : 𝕋) : 𝕋 :=
  let lc := maximum l one
  let uc := maximum u one
  neg (mulUp (divUp one lc) (divUp one uc))

/-- The largest of `g(l)`, `g(u)` and `g(min(max(1, l), u))`, `g(x) = 1 / max(x, 1) - m x`,
rounded up. -/
@[step_of reciprocalRelaxation]
def step_reciprocalHi (l u : 𝕋) : 𝕋 :=
  let m := step_reciprocalSlope l u
  let g := fun x => subUp (divUp one (maximum x one)) (mulDown m x)
  maximum (maximum (g l) (g u)) (g (minimum (maximum one l) u))

/-- The smaller of `g(l)` and `2 √(-m)`, rounded down. -/
@[step_of reciprocalRelaxation]
def step_reciprocalLo (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_reciprocalSlope l u
  let s := sqrtDownCora p (neg m)
  minimum (subDown (divDown one (maximum l one)) (mulUp m l)) (addDown s s)

/-- CORA.cpp's margin `w (1 + |m| max(|l|, |u|))`, rounded up. -/
@[step_of reciprocalRelaxation]
def step_reciprocalMargin (w l u : 𝕋) : 𝕋 :=
  let m := step_reciprocalSlope l u
  mulUp (addUp one (mulUp (absolute m) (maximum (absolute l) (absolute u)))) w


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `1 / max(x, 1) - m x` at the chord's slope, its middle and half its width plus the
margin. -/
def reciprocalRelaxation (p : ℕ) (w : 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofBand step_reciprocalSlope (step_reciprocalLo p) step_reciprocalHi
    (step_reciprocalMargin w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
