module

public import CORALean.NN.Layers.Operations.RelaxationOfBand
public import CORALean.Global.Float.SqrtDownCora
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The chord relaxation of the inverse

CORA.cpp's `priv_inverse_line` for `f(x) = 1 / x` on a box `[l, u]` with `0 < l`, with the lower
end from the closed-form minimum. The slope `m = -(1 / l)(1 / u)` is the chord's. `g(x) = 1/x - m x`
is convex, so on the box it is at most the larger of `g(l)` and `g(u)`; it is at least `2 √(-m)`,
the least `1/x - m x` takes for `x > 0`. The band goes to `Relaxation.ofBand` with CORA.cpp's
margin `w / l`; at round to nearest this is CORA.cpp's order.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor (CORA.cpp's `32 eps`)

## Output
* the chord relaxation of the inverse
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

/-- The chord's slope `-(1 / l)(1 / u)`, each quotient rounded up. -/
@[step_of inverseRelaxation]
def step_inverseSlope (l u : 𝕋) : 𝕋 :=
  neg (mulUp (divUp one l) (divUp one u))

/-- The larger of `g(l)` and `g(u)`, `g(x) = 1 / x - m x`, rounded up. -/
@[step_of inverseRelaxation]
def step_inverseHi (l u : 𝕋) : 𝕋 :=
  let m := step_inverseSlope l u
  let g := fun x => subUp (divUp one x) (mulDown m x)
  maximum (g l) (g u)

/-- `2 √(-m)`, rounded down. -/
@[step_of inverseRelaxation]
def step_inverseLo (p : ℕ) (l u : 𝕋) : 𝕋 :=
  let s := sqrtDownCora p (neg (step_inverseSlope l u))
  addDown s s

/-- CORA.cpp's margin `w / l`, rounded up. -/
@[step_of inverseRelaxation]
def step_inverseMargin (w l _u : 𝕋) : 𝕋 :=
  mulUp (divUp one l) w


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The band of `1 / x - m x` at the chord's slope, its middle and half its width plus the
margin. -/
def inverseRelaxation (p : ℕ) (w : 𝕋) : Relaxation 𝕋 :=
  Relaxation.ofBand step_inverseSlope (step_inverseLo p) step_inverseHi (step_inverseMargin w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
