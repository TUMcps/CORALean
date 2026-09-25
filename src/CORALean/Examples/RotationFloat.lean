import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachRecursiveFloatOuter
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# A continuous-time rotation, reached in floats both ways

`ẋ = [[0, 1], [-1, 0]] x`, the undamped clockwise rotation, from a box of
radius `1/16` around `(1, 0)`, over steps `Δt = 2⁻⁶`, at `Dyadic 64` and at
native `Float`: `LinearSys.reachFloat` (wrapping-free) and
`LinearSys.reachRecursiveFloat` (one step at a time), each with the guarantee
it carries against the exact flow. Every constant is a dyadic of a few bits, so
both scalars start from the same numbers.

The `#eval`s print, per window, the generator count, the half-width of the
interval hull in each coordinate, and the width of the error box: the quantity
the two schemes differ in, since the recursion multiplies the box by the
interval matrix every step and the wrapping-free run never does. Precision is
not checked here — the demo is where that happens.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


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
def summary {𝕋 : Type} [FloatOps 𝕋] (toF : 𝕋 → Float) (Z : Zonotope 𝕋 2) :
    ℕ × List String × List String :=
  let I := Z.interval
  (Z.h, List.ofFn fun i => sci ((toF (I.sup i) - toF (I.inf i)) / 2),
    List.ofFn fun i => sci (toF (Z.E.sup i) - toF (Z.E.inf i)))


/-! ## At `Dyadic 64` -/

def sysD : LinearSys (Dyadic 64) 2 := ⟨!![d 0 0, d 1 0; d (-1) 0, d 0 0]⟩

def X₀D : Zonotope (Dyadic 64) 2 where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-4), d 0 0; d 0 0, d 1 (-4)]
  E := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

def ΔtD : Dyadic 64 := d 1 (-6)

/-- Eight windows, Taylor order at least `4`, the first window reduced to order `10`. -/
def wrapFreeD : Option (List (Zonotope (Dyadic 64) 2)) := sysD.reachFloat X₀D ΔtD 4 10 8

/-- The same settings, one step at a time: the windows, then `R_0, …, R_8`. -/
def recursiveD : Option (List (Zonotope (Dyadic 64) 2) × List (Zonotope (Dyadic 64) 2)) :=
  sysD.reachRecursiveFloat X₀D ΔtD 4 10 8

theorem ΔtD_pos : 0 < toReal ΔtD := by
  show 0 < Dyadic.toReal ΔtD
  rw [Dyadic.toReal_def]
  norm_num [ΔtD, d]

/-- What a successful wrapping-free run is worth: the exact flow, over every window. -/
example {Rs : List (Zonotope (Dyadic 64) 2)} (h : wrapFreeD = some Rs) :=
  sysD.reachFloat_outer ΔtD_pos h

/-- And the recursive one's, over every window. -/
example {Rti Rtp : List (Zonotope (Dyadic 64) 2)} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachRecursiveFloat_outer ΔtD_pos h

/-- And at every step, where `Δt` need not even be positive. -/
example {Rti Rtp : List (Zonotope (Dyadic 64) 2)} (h : recursiveD = some (Rti, Rtp)) :=
  sysD.reachRecursiveFloat_timePoint_outer h


/-! ## At native `Float` -/

def sysF : LinearSys Float 2 := ⟨!![0.0, 1.0; -1.0, 0.0]⟩

def X₀F : Zonotope Float 2 where
  h := 2
  c := ![1.0, 0.0]
  G := !![0.0625, 0.0; 0.0, 0.0625]
  E := ⟨fun _ => 0.0, fun _ => 0.0⟩

def ΔtF : Float := 0.015625


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Dyadic runs' settings at binary64. -/
def wrapFreeF : Option (List (Zonotope Float 2)) := sysF.reachFloat X₀F ΔtF 4 10 8

def recursiveF : Option (List (Zonotope Float 2) × List (Zonotope Float 2)) :=
  sysF.reachRecursiveFloat X₀F ΔtF 4 10 8

#eval wrapFreeD.map (·.map (summary dToFloat))
#eval recursiveD.map fun r => r.1.map (summary dToFloat)
#eval recursiveD.map fun r => r.2.map (summary dToFloat)
#eval wrapFreeF.map (·.map (summary id))
#eval recursiveF.map fun r => r.1.map (summary id)
#eval recursiveF.map fun r => r.2.map (summary id)

end CORALean.RotationFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
