module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptiveOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptiveState

@[expose] public section

/-!
# The state of CORA's `reach_adaptive` before its first step, at `'poly'`

`options` as `reach_adaptive` sets them before its first step: `options.i = 1`, `options.t =
params.tStart`, `options.R = params.R0`, and the admissible errors zero.

## Inputs
* `o` – adaptive options
* `R0` – start polynomial zonotope

## Output
* the state before the first step
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `options` as `reach_adaptive` sets them before its first step, from `R0`. -/
def NonlinearSys.linReachPolyAdaptiveInit (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (R0 : PolyZonotope (Vec 𝕋 n)) : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n :=
  { i := 1, t := o.tStart, R := R0, Rτ := R0,                       -- options.i, .t, .R
    timeStep := zero, finitehorizon := zero, varphi := zero,
    errAdmHorizon := fun _ => zero, errAdmDeltatopt := fun _ => zero,  -- zeros(nrOfDims,1)
    orders := fun _ => none, minorder := 0, zeroWidthDim := fun _ => false, steps := [] }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
