module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.Global.Float.SqrtDownCora
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The chord relaxation of the cube

CORA.cpp's `priv_cube_line` for `f(x) = x³` on a box `[l, u]`. The slope `m = l² + l u + u²` is the
chord's. `g(x) = x³ - m x` is extreme on the box at its ends and at `±s` clamped into it,
`s = √(m / 3)` the stationary point. The root is taken from below and from above, from `m (1 / 3)`
rounded each way (CORA.cpp's order), and `g` at the clamped point is bounded
over the clamped pair; at round to nearest both are one value. The band goes to `Relaxation.ofBand`
with CORA.cpp's margin `w max(|l|, |u|)³`; at round to nearest this is CORA.cpp's order.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor (CORA.cpp's `64 eps`)

## Output
* the chord relaxation of the cube
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

/-- `x³` from above, as CORA.cpp's `x² x`: the square rounded either way, the larger product. -/
@[step_of cubeRelaxation]
def step_cubeUp (x : 𝕋) : 𝕋 :=
  maximum (mulUp (mulUp x x) x) (mulUp (mulDown x x) x)

/-- `x³` from below: the square rounded either way, the smaller product. -/
@[step_of cubeRelaxation]
def step_cubeDown (x : 𝕋) : 𝕋 :=
  minimum (mulDown (mulDown x x) x) (mulDown (mulUp x x) x)

/-- The chord's slope `(l² + l u) + u²`. -/
@[step_of cubeRelaxation]
def step_cubeSlope (l u : 𝕋) : 𝕋 :=
  addUp (addUp (mulUp l l) (mulUp l u)) (mulUp u u)

/-- The stationary point `√(m / 3)` from below, from `m (1 / 3)` rounded down. -/
@[step_of cubeRelaxation]
def step_cubeRootDown (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let three := addUp one (addUp one one)
  sqrtDownCora p (mulDown (step_cubeSlope l u) (divDown one three))

/-- The stationary point `√(m / 3)` from above, from `m (1 / 3)` rounded up (a third of a divisor
not certified positive is taken as `1`). -/
@[step_of cubeRelaxation]
def step_cubeRootUp (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let three := addDown one (addDown one one)
  let third := if ltStrict zero three then divUp one three else one
  sqrtUp p (mulUp (step_cubeSlope l u) third)

/-- `x` clamped into `[l, u]`. -/
@[step_of cubeRelaxation]
def step_cubeClamp (l u x : 𝕋) : 𝕋 := minimum (maximum x l) u

/-- `g(x) = x³ - m x` over `[a, b]` from above (for `m ≥ 0`; at any `m` where `a = b`). -/
@[step_of cubeRelaxation]
def step_cubeGUp (m a b : 𝕋) : 𝕋 := subUp (step_cubeUp b) (mulDown m a)

/-- `g` over `[a, b]` from below (for `m ≥ 0`; at any `m` where `a = b`). -/
@[step_of cubeRelaxation]
def step_cubeGDown (m a b : 𝕋) : 𝕋 := subDown (step_cubeDown a) (mulUp m b)

/-- The largest of `g` at `l`, `u`, the clamped root and its clamped negative, rounded up. -/
@[step_of cubeRelaxation]
def step_cubeHi (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_cubeSlope l u
  let sa := step_cubeRootDown p l u
  let sb := step_cubeRootUp p l u
  let c := step_cubeClamp l u
  maximum (maximum (step_cubeGUp m l l) (step_cubeGUp m u u))
    (maximum (step_cubeGUp m (c sa) (c sb)) (step_cubeGUp m (c (neg sb)) (c (neg sa))))

/-- The least of `g` at the same four points, rounded down. -/
@[step_of cubeRelaxation]
def step_cubeLo (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let m := step_cubeSlope l u
  let sa := step_cubeRootDown p l u
  let sb := step_cubeRootUp p l u
  let c := step_cubeClamp l u
  minimum (minimum (step_cubeGDown m l l) (step_cubeGDown m u u))
    (minimum (step_cubeGDown m (c sa) (c sb)) (step_cubeGDown m (c (neg sb)) (c (neg sa))))

/-- CORA.cpp's margin `w max(|l|, |u|)³`, rounded up. -/
@[step_of cubeRelaxation]
def step_cubeMargin (w l u : 𝕋) : 𝕋 :=
  let big := maximum (absolute l) (absolute u)
  mulUp (mulUp (mulUp big big) big) w


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `x³ - m x` at the chord's slope, its middle and half its width plus the margin. -/
def cubeRelaxation (p : ℕ) (w : 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofBand step_cubeSlope (step_cubeLo p) (step_cubeHi p) (step_cubeMargin w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
