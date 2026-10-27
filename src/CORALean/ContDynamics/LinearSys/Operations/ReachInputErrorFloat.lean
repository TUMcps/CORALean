module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorBoxFloat
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Global.StepOf

@[expose] public section

/-!
# What a sampled run's input enclosures owe, in floats

`reachInputError` computed in `𝕋`: every step's error box, each carried forward by one
`[e^{AΔt}]` per step taken since. The accumulator is a float zonotope that *encloses* the exact
one — the box paid at each step is rounded up, and the exponential is the interval matrix that
holds `e^{AΔt}` — which is the direction an inner approximation needs of what it takes off.

## Inputs
* `sys` – linear system
* `Δt` – float sampling step
* `η` – Taylor order
* `U` – input float zonotope
* `k` – number of steps

## Output
* float accumulated error boxes of the input enclosures
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `k` steps of the recursion, from `[e^{AΔt}]` and the box paid at each step. -/
@[step_of LinearSys.reachInputErrorFloat]
def step_reachInputErrorFloat (eAΔt : Interval (Mat 𝕋 n n)) (box : Zonotope (Vec 𝕋 n)) :
    ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Zonotope.point fun _ => zero
  | k + 1 =>
    Plus.plus (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAΔt
      (step_reachInputErrorFloat eAΔt box k)) box


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the input enclosures of `k` sampled steps owe together, enclosing the exact
`reachInputError`. -/
def LinearSys.reachInputErrorFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ)
    (U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                          -- [e^{AΔt}]
  let box := sys.timePointStepErrorBoxFloat Δt η U                -- paid afresh at every step
  step_reachInputErrorFloat eAΔt box k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
