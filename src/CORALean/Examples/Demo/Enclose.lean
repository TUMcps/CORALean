import CORALean.Examples.FeedForwardFloat
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.Examples.Demo.Decimal
import CORALean.Examples.Demo.Scalar

/-!
# `NeuralNetwork.enclose` at `Dyadic`, run

`Examples.FeedForwardFloat`'s network — affine, ReLU, affine — at `Dyadic 24`,
with an input box wide enough that all three hidden neurons cross zero, which is
where a ReLU relaxation costs anything at all.

`layerBoxes` is `enclose`'s own recursion with a line printed between the
steps, so the last line it prints and the `enclose` line under it are the same
computation reached two ways; they agree or the table says so.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- `x ↦ [x₁ + x₂ - 1/2, x₁ - x₂, -x₁ + x₂ + 1/4]`. -/
def W₁ : Mat D 3 2 := !![dy 1 0, dy 1 0; dy 1 0, dy (-1) 0; dy (-1) 0, dy 1 0]

def b₁ : Vec D 3 := ![dy (-1) (-1), dy 0 0, dy 1 (-2)]

/-- `y ↦ [y₁ - y₂ + y₃/2, y₁/2 + y₂ - y₃ + 1/8]`. -/
def W₂ : Mat D 2 3 := !![dy 1 0, dy (-1) 0, dy 1 (-1); dy 1 (-1), dy 1 0, dy (-1) 0]

def b₂ : Vec D 2 := ![dy 0 0, dy 1 (-3)]

def net : Real.NeuralNetwork (Zonotope D) 2 2 := Example.feedForward W₁ b₁ W₂ b₂

/-- `[-1, 1]²`. -/
def X : Zonotope D 2 where
  h := 2
  c := ![dy 0 0, dy 0 0]
  G := !![dy 1 0, dy 0 0; dy 0 0, dy 1 0]
  E := zeroBox 2

def layerLine (i : ℕ) {n : ℕ} (Z : Zonotope D n) : String :=
  pad 6 (toString i) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

/-- One line per layer, the set handed on being the set printed. -/
def layerBoxes : {n m : ℕ} → Real.NeuralNetwork (Zonotope D) n m → Zonotope D n → ℕ →
    List String
  | _, _, .nil, _, _ => []
  | _, _, .cons L rest, Z, i =>
    let Y := L.enclose Z
    layerLine i Y :: layerBoxes rest Y (i + 1)


-- =====================================  MAIN DEFINITION  ====================================== --

def encloseReport : String :=
  String.intercalate "\n" ([
    "== NeuralNetwork.enclose at Dyadic 24 ==",
    "",
    "affine 2 -> 3, ReLU, affine 3 -> 2, as in Examples.FeedForwardFloat",
    "X = [-1, 1]^2",
    "",
    " layer  gens  Zonotope.interval of the set that layer hands on",
    layerLine 0 X] ++
    layerBoxes net X 1 ++ [
    "",
    "enclose  " ++ showBox (net.enclose X).interval])

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
