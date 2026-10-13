import CORALean.Examples.Demo.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Demo.Decimal
import CORALean.Global.Float.Instances.Binary64.Instances
import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
import CORALean.Global.Float.Instances.Dyadic.Operations.Neg
import CORALean.Global.Float.NoNaN

/-!
# The same run at native binary64

`LinearSysDT.reach` a third time, on the system `Reach` defines, at Lean's
`Float` rather than at `Dyadic`. Every constant is a four-bit dyadic and is
therefore exact in binary64 too, so the two runs start from the same numbers
and any difference between the tables is the arithmetic.

There is one, and it is the price of directed rounding without a hardware
rounding mode: `Binary64.addUp` is the machine's round-to-nearest sum stepped
one unit in the last place up, so every operation widens whether or not it had
to. `Dyadic 24` carries the whole run exactly and reports a zero error box;
here the box is nonzero from the first step. It is around `2 ^ -50`, which nine
decimal places cannot show, so the widths are printed as the dyadics they are.

What this does not show is the difference that matters: at `Dyadic` the bounds
are theorems, and here they rest on the one axiom `Axioms` states.
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- `[[15/16, -1/8], [1/8, 15/16]]` again, written in decimal because that is
what a `Float` literal takes; all four entries are exact in binary64. -/
def Ab : Mat Float 2 2 := !![0.9375, -0.125; 0.125, 0.9375]

def sysb : LinearSysDT Float 2 := ⟨Ab⟩

/-- Zero width in every coordinate, as `zeroBox` is at `Dyadic`. -/
def zeroBoxB (n : ℕ) : Interval (Vec Float n) := ⟨fun _ => 0.0, fun _ => 0.0⟩

/-- `[0.875, 1.125] × [-0.125, 0.125]`. -/
def R₀b : Zonotope (Vec Float 2) where
  h := 2
  c := ![1.0, 0.0]
  G := !![0.125, 0.0; 0.0, 0.125]
  E := zeroBoxB 2

/-- `[-1/64, 1/64]²`. -/
def Ub : Zonotope (Vec Float 2) where
  h := 2
  c := ![0.0, 0.0]
  G := !![0.015625, 0.0; 0.0, 0.015625]
  E := zeroBoxB 2

/-- The same `order` and the same `steps` as the `Dyadic` runs, so the three
tables are the same computation and nothing else. -/
def Rb (k : ℕ) : Zonotope (Vec Float 2) :=
  sysb.reach (S := fun k => Zonotope (Vec Float k)) ⟨R₀b, Ub, 0, k⟩ ⟨order, by decide⟩

/-! ## On the page

A finite `Float` is a dyadic, so the decimals are `Decimal`'s, taken through the
bit decoding and rounded outward exactly as the `Dyadic` tables are. -/

def showBoundB {n : ℕ} (I : Interval (Vec Float n)) (i : Fin n) : String :=
  "[" ++ pad 14 (showDown (Binary64.toDyadic (I.inf i))) ++ "," ++
    pad 15 (showUp (Binary64.toDyadic (I.sup i))) ++ " ]"

def showBoxB {n : ℕ} (I : Interval (Vec Float n)) : String :=
  String.intercalate " " (List.ofFn fun i => showBoundB I i)

/-- `m · 2 ^ e`, written out. The error box here is a few units in the last
place, which no fixed number of decimals displays, and which is the one quantity
this run exists to show. -/
def showExact (d : Dyadic 53) : String :=
  if d.mantissa = 0 then "0" else toString d.mantissa ++ "*2^" ++ toString d.exponent

/-- `Rb k` if no float of it is a NaN. The table reports a hardware run only then, which is
what the trust base asks of a `Float` result (README, item 2); `ifNoNaN` makes the test. -/
def RbChecked (k : ℕ) : Option (Zonotope (Vec Float 2)) := ifNoNaN (𝕋 := Float) (Rb k)

def reachRowB (k : ℕ) : String :=
  match RbChecked k with
  | none => pad 4 (toString k) ++ "rejected: a float of the result is a NaN"
  | some Z => pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBoxB Z.interval

/-- The width of one coordinate of the error box, differenced as dyadics rather
than as floats: `subUp` would add a step of its own and report the width of a
box that is exactly zero as one unit in the last place. -/
def widthB {n : ℕ} (I : Interval (Vec Float n)) (i : Fin n) : Dyadic 53 :=
  Dyadic.exactAdd (Binary64.toDyadic (I.sup i))
    (CORALean.Float.Dyadic.neg (Binary64.toDyadic (I.inf i)))

def errorRowB (k : ℕ) : String :=
  match RbChecked k with
  | none => pad 4 (toString k) ++ "rejected: a float of the result is a NaN"
  | some Z =>
    pad 4 (toString k) ++ pad 28 (showExact (widthB Z.E 0)) ++ pad 26 (showExact (widthB Z.E 1))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The third table `main` prints: the reachable set at `Float`, beside the
error box the one-ulp steps accumulate into. -/
def reachReportBinary64 : String :=
  String.intercalate "\n" ([
    "== LinearSysDT.reach at native binary64 ==",
    "",
    "the same A, R0, U and order as above, every constant exact in binary64",
    "",
    "Zonotope.interval of the reachable set, nominal part and error box together:",
    "",
    "   k  gens  x1                              x2"] ++
    (List.range (steps + 1)).map reachRowB ++ [
    "",
    "the error box alone, as an exact width per coordinate:",
    "",
    "   k                     width 1                   width 2"] ++
    (List.range (steps + 1)).map errorRowB)

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
