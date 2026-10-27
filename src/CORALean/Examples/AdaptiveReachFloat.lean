import CORALean.ContDynamics.LinearSys.Theorems.ReachAdaptiveFloatOuter
import CORALean.Examples.RotationFloat
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# Adaptive reachability in floats, the steps it chose

A damped rotation driven by an input on the second state, `ẋ = [[-2, 2], [-2, -2]] x + [0; 1] u`,
`u(t) ∈ [3/8, 5/8]`, from `RotationFloat`'s box over `[0, 1]` at `Dyadic 64`, with
`LinearSys.reachAdaptiveFloat`, [1, Alg. 1], choosing every step size, truncation order and
reduction order against [1]'s budgets `ε_H,max = 1/100`, `ε_P,max = 1/1000`, `ε_S,max = 1/50`. The
`#eval` prints, per step, the window, `Δt_i`, `Φ_prop,i`, `Φ_set,i`, `ε_H` and the accumulated
`ε_P`, `ε_S`. The damping shrinks `ε_H` as `t_i` grows, so the step doubles once it can, and the
last step lands on `t_f`.

## Inputs
* `q` – rational number

## Output
* the nearest double to the rational

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.AdaptiveReachFloat

open CORALean CORALean.Float CORALean.RotationFloat

/-- The damped rotation. -/
def sysD : LinearSys (Dyadic 64) 2 := LinearSys.canonicalFloat
    (!![d (-2) 0, d 2 0; d (-2) 0, d (-2) 0])

/-- The input enters the second state alone. -/
def BD : Mat (Dyadic 64) 2 1 := !![d 0 0; d 1 0]

/-- The damped rotation with that input, CORA's `linearSys(A, BD)`: `c = 0`, the output the
state. -/
def sysBD : LinearSys (Dyadic 64) 2 := { sysD with m := 1, B := BD, D := fun _ _ => d 0 0 }

/-- `[3/8, 5/8]`, centered at `1/2`: `0` is not in it. -/
def UD : Zonotope (Vec (Dyadic 64) 1) where
  h := 1
  c := ![d 1 (-1)]
  G := !![d 1 (-3)]
  I_error := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- [1]'s three budgets, `μ = 1/2`, orders up to `6`, and the two loop bounds. -/
def optionsD : LinearSys.AdaptiveOptions (Dyadic 64) :=
  { εHmax := 1 / 100, εPmax := 1 / 1000, εSmax := 1 / 50, μ := d 1 (-1), ηmax := 6,
    fuel := 30, maxSteps := 100 }

/-- `[0, 1]`, every parameter tuned. -/
def adaptiveD : Option (List (LinearSys.AdaptiveStepInfo (Dyadic 64) 2)) :=
  sysBD.reachAdaptiveFloat { X₀ := X₀D, U := UD, tFinal := 1 } optionsD

/-- What a successful run is worth: its windows cover `[0, 1]`, and every run
under every input signal in `B U` is in the window of every time. -/
example {steps : List (LinearSys.AdaptiveStepInfo (Dyadic 64) 2)} (h : adaptiveD = some steps) :=
  sysBD.reachAdaptiveFloat_outer _ h


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A rational, through `Float`, for printing only. -/
def qToFloat (q : ℚ) : Float := Float.ofInt q.num / q.den.toFloat

/-- One step: `[t_i, t_{i+1}]`, `Δt_i`, `Φ_prop,i`, `Φ_set,i`, `ε_H`, `ε_P`, `ε_S`,
and the window's hull half-widths. -/
def report (r : LinearSys.AdaptiveStepInfo (Dyadic 64) 2) :
    String × String × ℕ × ℕ × List String × List String :=
  let I := r.R.interval
  (s!"[{r.tStart}, {r.tEnd}]", toString (dToFloat r.Δt), r.η, r.ρ,
    [sci (qToFloat r.εH), sci (qToFloat r.εP), sci (qToFloat r.εS)],
    List.ofFn fun i => sci ((dToFloat (I.sup i) - dToFloat (I.inf i)) / 2))

#eval adaptiveD.map (·.map report)

end CORALean.AdaptiveReachFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
