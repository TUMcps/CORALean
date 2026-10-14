import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputTimePointOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeFloatInputOuter
import CORALean.Examples.RotationFloat

/-!
# The rotation driven by an input, reached in floats both ways

`RotationFloat`'s system with an input on the second state,
`ẋ = [[0, 1], [-1, 0]] x + [0; 1] u`, `u(t) ∈ [3/8, 5/8]` arbitrary in time —
an input set that does not hold `0` — from the same box, over the same eight
steps at `Dyadic 64`: `LinearSys.reachFloatInput` (CORA's standard scheme) and
`LinearSys.reachWrappingFreeFloatInput`, each with the guarantee it carries
against every run. The `#eval`s print the summary `RotationFloat` prints, and
the time-point sets' centres, the second falling at `-x₁ + 1/2`, half the rate
it falls at without the input.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RotationInputFloat

open CORALean CORALean.Float CORALean.RotationFloat

/-- The input enters the second state alone. -/
def BD : Mat (Dyadic 64) 2 1 := !![d 0 0; d 1 0]

/-- `[3/8, 5/8]`, centred at `1/2`: `0` is not in it. -/
def UD : Zonotope (Vec (Dyadic 64) 1) where
  h := 1
  c := ![d 1 (-1)]
  G := !![d 1 (-3)]
  I_error := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- `[0, 1/8]` in eight windows, Taylor order at least `4`, order `10`: the windows,
then `R_0, …, R_8`. -/
def recursiveD : Option (List (Zonotope (Vec (Dyadic 64) 2)) × List
    (Zonotope (Vec (Dyadic 64) 2))) :=
  sysD.reachFloatInput BD { X₀ := X₀D, U := UD, tFinal := 1 / 8 }
    { Δt := ΔtD, η := 4, ρ := 10 }

/-- The same settings, each window from the first by `[e^{A t_k}]`. -/
def wrapFreeD : Option (List (Zonotope (Vec (Dyadic 64) 2))) :=
  sysD.reachWrappingFreeFloatInput BD { X₀ := X₀D, U := UD, tFinal := 1 / 8 }
    { Δt := ΔtD, η := 4, ρ := 10 }

/-- What a successful recursive run is worth: every run under every input signal
in `B U`, over every window. -/
example {Rti Rtp : List (Zonotope (Vec (Dyadic 64) 2))} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachFloatInput_outer BD h

/-- And at every step. -/
example {Rti Rtp : List (Zonotope (Vec (Dyadic 64) 2))} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachFloatInput_timePoint_outer BD h

/-- And the wrapping-free run's, over every window. -/
example {Rs : List (Zonotope (Vec (Dyadic 64) 2))} (h : wrapFreeD = some Rs) :=
  sysD.reachWrappingFreeFloatInput_outer BD h


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-point sets' centres, through `Float`. -/
def centres (Rs : List (Zonotope (Vec (Dyadic 64) 2))) : List (List Float) :=
  Rs.map fun Z => List.ofFn fun i => dToFloat (Z.c i)

#eval recursiveD.map fun r => r.1.map (summary dToFloat)
#eval recursiveD.map fun r => r.2.map (summary dToFloat)
#eval recursiveD.map fun r => centres r.2
#eval wrapFreeD.map (·.map (summary dToFloat))

end CORALean.RotationInputFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
