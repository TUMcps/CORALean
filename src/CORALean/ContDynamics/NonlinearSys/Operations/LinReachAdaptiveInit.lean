module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveState

@[expose] public section

/-!
# The state CORA's `reach_adaptive` starts from

`reach_adaptive`'s initialization before its main loop: `options.i = 1`, `options.t = tStart`,
`options.R = R0`, both admissible errors zero; the fields the first step writes before it reads
them start at zero, the tensor order at `2` (the first step decides it).

## Inputs
* `o` – adaptive options
* `R0` – initial set

## Output
* the state of step `1`
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `options` as `reach_adaptive` sets them before its first step, from `R0`. -/
def NonlinearSys.linReachAdaptiveInit (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (R0 : Zonotope (Vec 𝕋 n)) : NonlinearSys.LinReachAdaptiveState 𝕋 n :=
  { i := 1, t := o.tStart, R := R0, Rτ := R0,                       -- options.i, .t, .R
    timeStep := zero, finitehorizon := zero, varphi := zero,
    errAdmHorizon := fun _ => zero, errAdmDeltatopt := fun _ => zero,  -- zeros(nrOfDims,1)
    tensorOrder := 2, orders := fun _ => none, minorder := 0, zeroWidthDim := fun _ => false,
    kappaDeltat := zero, kappaAbstrerr := zero, steps := [] }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
