import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.Canonical
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepFloat
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Demo.Decimal
import CORALean.Examples.Demo.Scalar
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# One `LinParamSys` step at an interval matrix, run

`ẋ = A x + u` with `A` anywhere in a box of half-width `1/16` around
`[[-1, 1]; [0, -2]]`, one step of `Δt = 1/8` at Taylor order `4`, from the
initial box `R0` with inputs in `U`. The float step `timeIntervalStepFloat` and
input solution `inputSolutionFloat` are the sets both readings get:
`'constParam'` by `ConstTrajectory`, `'varParam'`, a fresh member at every
instant, by `Trajectory.timeIntervalStepFloat_outer` and its input counterpart.
Proved the same set, so there is nothing to compare between the readings.

What is shown is what the matrix uncertainty costs: the same step at the point
box, the center matrix alone, beside it, and the widths of each.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- The box around `[[-1, 1]; [0, -2]]`, half-width `1/16` in every entry. -/
def paramA : Interval (Mat D 2 2) :=
  ⟨!![dy (-17) (-4), dy 15 (-4); dy (-1) (-4), dy (-33) (-4)],
   !![dy (-15) (-4), dy 17 (-4); dy 1 (-4), dy (-31) (-4)]⟩

/-- The center matrix alone, as a point box. -/
def pointA : Interval (Mat D 2 2) :=
  ⟨!![dy (-1) 0, dy 1 0; dy 0 0, dy (-2) 0], !![dy (-1) 0, dy 1 0; dy 0 0, dy (-2) 0]⟩

/-- `[0.875, 1.125] × [-0.125, 0.125]`. -/
def paramR₀ : Zonotope (Vec D 2) where
  h := 2
  c := ![dy 1 0, dy 0 0]
  G := !![dy 1 (-3), dy 0 0; dy 0 0, dy 1 (-3)]
  I_error := zeroBox 2

/-- `[-1/64, 1/64]²`. -/
def paramU : Zonotope (Vec D 2) where
  h := 2
  c := ![dy 0 0, dy 0 0]
  G := !![dy 1 (-6), dy 0 0; dy 0 0, dy 1 (-6)]
  I_error := zeroBox 2

/-- The step size, `1/8`. -/
def paramΔt : D := dy 1 (-3)

/-- The step's homogeneous set and input solution at a matrix box. -/
def paramStep (B : Interval (Mat D 2 2)) : Zonotope (Vec D 2) × Zonotope (Vec D 2) :=
  let sys : LinParamSys ℐ[D] 2 := LinParamSys.canonical B
  (sys.timeIntervalStepFloat paramΔt 4 paramR₀, sys.inputSolutionFloat paramΔt 4 paramU)

/-- One row: the set as a box, and its widths. -/
def paramRow (name : String) (Z : Zonotope (Vec D 2)) : String :=
  pad 10 name ++ "  " ++ showBox Z.interval ++ "  " ++ pad 14 (showWidth Z.interval 0)
    ++ pad 15 (showWidth Z.interval 1)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The report: the step at the box and at its center, homogeneous part and input. -/
def paramReport : String :=
  let box := paramStep paramA
  let pt := paramStep pointA
  String.intercalate "\n" [
    "== LinParamSys.timeIntervalStepFloat at Dyadic 24 ==",
    "",
    "A  in [ -1  1 ; 0  -2 ] +- 1/16 entrywise, constParam and varParam alike",
    "R0 = [0.875, 1.125] x [-0.125, 0.125],  U = [-0.015625, 0.015625]^2",
    "dt = 1/8, Taylor order 4",
    "",
    "            x1                              x2                                width 1"
      ++ "        width 2",
    paramRow "step, box" box.1,
    paramRow "step, A0" pt.1,
    paramRow "input, box" box.2,
    paramRow "input, A0" pt.2]

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
