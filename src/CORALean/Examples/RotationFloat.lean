import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatOuter
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.Global.Float.Instances.Binary64.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# A continuous-time rotation, reached in floats both ways

`ẋ = [[0, 1], [-1, 0]] x`, the undamped clockwise rotation, from a box of radius `1/16` around
`(1, 0)`, over steps `Δt = 2⁻⁶`, at `Dyadic 64` and at native `Float`:
`LinearSys.reachWrappingFreeFloat` and `LinearSys.reachFloat` (one step at a time), each with the
guarantee it carries against the exact flow. Every constant is a dyadic of a few bits, so both
scalars start from the same numbers. The `#eval`s print, per window, the generator count, the
half-width of the interval hull in each coordinate, and the width of the error box: the quantity
the two schemes differ in, since the recursion multiplies the box by the interval matrix every step
and the wrapping-free run never does.

## Inputs
* none

## Output
* wrapping-free float reach sets at native Float
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RotationFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : Dyadic 64 := ⟨m, e⟩

/-- The same scalar read as a machine double, for printing only. -/
def dToFloat (x : Dyadic 64) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent

/-- `x` as `m.mmme±k`, three significant digits: the error box spans twenty
orders of magnitude between the two scalars, which a fixed-point print hides. -/
def sci (x : Float) : String :=
  if x == 0 then "0" else
    let k := (Float.log10 x.abs).floor
    let m := (x / Float.pow 10 k * 1000).round / 1000
    toString m ++ "e" ++ toString k.toInt64

/-- Generators, the hull's half-width per coordinate, and the error box's width
per coordinate, printed through `Float`. -/
def summary {𝕋 : Type} [FloatOps 𝕋] (toF : 𝕋 → Float) (Z : Zonotope (Vec 𝕋 2)) :
    ℕ × List String × List String :=
  let I := Z.interval
  (Z.h, List.ofFn fun i => sci ((toF (I.sup i) - toF (I.inf i)) / 2),
    List.ofFn fun i => sci (toF (Z.I_error.sup i) - toF (Z.I_error.inf i)))


/-! ## At `Dyadic 64` -/

def sysD : LinearSys (Dyadic 64) 2 := LinearSys.canonicalFloat (!![d 0 0, d 1 0; d (-1) 0, d 0 0])

def X₀D : Zonotope (Vec (Dyadic 64) 2) where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-4), d 0 0; d 0 0, d 1 (-4)]
  I_error := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

def ΔtD : Dyadic 64 := d 1 (-6)

/-- `[0, 1/8]` in eight windows, Taylor order at least `4`, the first window reduced to
order `10`. -/
def wrapFreeD : Option (List (Zonotope (Vec (Dyadic 64) 2))) :=
  sysD.reachWrappingFreeFloat { X₀ := X₀D, tFinal := 1 / 8 }
    { Δt := ΔtD, η := 4, ρ := 10 }

/-- The same settings, one step at a time: the windows, then `R_0, …, R_8`. -/
def recursiveD : Option (List (Zonotope (Vec (Dyadic 64) 2)) × List
    (Zonotope (Vec (Dyadic 64) 2))) :=
  sysD.reachFloat { X₀ := X₀D, tFinal := 1 / 8 }
    { Δt := ΔtD, η := 4, ρ := 10 }

/-- What a successful wrapping-free run is worth: the exact flow, over every window,
`1/8 = 8 Δt` split into the eight windows `Reach.steps` derived. -/
example {Rs : List (Zonotope (Vec (Dyadic 64) 2))} (h : wrapFreeD = some Rs) :=
  sysD.reachWrappingFreeFloat_outer _ h

/-- And the recursive one's, over every window. -/
example {Rti Rtp : List (Zonotope (Vec (Dyadic 64) 2))} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachFloat_outer _ _ h

/-- And at every step. -/
example {Rti Rtp : List (Zonotope (Vec (Dyadic 64) 2))} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachFloat_timePoint_outer _ _ h


/-! ## At native `Float` -/

def sysF : LinearSys Float 2 := LinearSys.canonicalFloat !![0.0, 1.0; -1.0, 0.0]

def X₀F : Zonotope (Vec Float 2) where
  h := 2
  c := ![1.0, 0.0]
  G := !![0.0625, 0.0; 0.0, 0.0625]
  I_error := ⟨fun _ => 0.0, fun _ => 0.0⟩

def ΔtF : Float := 0.015625


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Dyadic runs' settings at binary64. -/
def wrapFreeF : Option (List (Zonotope (Vec Float 2))) :=
  sysF.reachWrappingFreeFloat { X₀ := X₀F, tFinal := 1 / 8 }
    { Δt := ΔtF, η := 4, ρ := 10 }

/-- The one-step-at-a-time reach of the `Float` system over the same time and step. -/
def recursiveF : Option (List (Zonotope (Vec Float 2)) × List (Zonotope (Vec Float 2))) :=
  sysF.reachFloat { X₀ := X₀F, tFinal := 1 / 8 }
    { Δt := ΔtF, η := 4, ρ := 10 }

#eval wrapFreeD.map (·.map (summary dToFloat))
#eval recursiveD.map fun r => r.1.map (summary dToFloat)
#eval recursiveD.map fun r => r.2.map (summary dToFloat)
#eval wrapFreeF.map (·.map (summary id))
#eval recursiveF.map fun r => r.1.map (summary id)
#eval recursiveF.map fun r => r.2.map (summary id)

end CORALean.RotationFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
