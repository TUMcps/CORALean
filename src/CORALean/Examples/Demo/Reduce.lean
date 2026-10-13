import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.Examples.Demo.Decimal
import CORALean.Examples.Demo.Scalar
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.RelaxationBox
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Theorems.ReluRelaxationSound
import CORALean.NN.Operations.Enclose
import CORALean.NN.Operations.ReduceOnTheFly
import CORALean.NN.Operations.ReducibleNetworkToNetwork

/-!
# [1, Alg. 2] at `Dyadic`, run

A network with four hidden ReLU neurons, two of which the input box `X` leaves at or near
zero: one never fires, the other fires by at most `1/16`. At `ρ = 1/2` [1, Alg. 1] has to
merge two, and the static bucket at `0` finds exactly those; the reduced network then runs
through two hidden neurons, and what the merged pair could have contributed arrives as the
error box [1, Eq. 2] adds to the next linear layer.

The unreduced network's enclosure is printed beside the reduced one's. Both contain the exact
image — `enclose_outer` and `reduceOnTheFly_outer` — and the reduced one pays for its merged
neurons with a box, which forgets how they depend on the input.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- `x ↦ [x₁ + x₂, -x₁ - x₂ - 2, x₁ - x₂, (x₂ - x₁ + 1)/8]`. -/
def Wr₁ : Mat D 4 2 :=
  !![dy 1 0, dy 1 0; dy (-1) 0, dy (-1) 0; dy 1 0, dy (-1) 0; dy (-1) (-3), dy 1 (-3)]

def br₁ : Vec D 4 := ![dy 0 0, dy (-2) 0, dy 0 0, dy 1 (-3)]

/-- `y ↦ [y₁ + y₂ + y₃ + y₄, y₁ - y₃/2 + 4 y₄]`. -/
def Wr₂ : Mat D 2 4 := !![dy 1 0, dy 1 0, dy 1 0, dy 1 0; dy 1 0, dy 0 0, dy (-1) (-1), dy 4 0]

def br₂ : Vec D 2 := ![dy 0 0, dy 0 0]

/-- Affine, ReLU, affine, ReLU, every error box `[0, 0]` and both buckets static at `0`. -/
def reducible : ReducibleNetwork D 2 2 :=
  .cons ⟨Wr₁, br₁, zeroBox 4⟩ (reluRelaxation reluSlope) ⟨_, reluRelaxation_sound reluSlope⟩
      (.static [dy 0 0])
    (.cons ⟨Wr₂, br₂, zeroBox 2⟩ (reluRelaxation reluSlope) ⟨_, reluRelaxation_sound reluSlope⟩
      (.static [dy 0 0]) .nil)

/-- `[1, 2] × [0, 1/2]`. -/
def Xr : Zonotope (Vec D 2) where
  h := 2
  c := ![dy 3 (-1), dy 1 (-2)]
  G := !![dy 1 (-1), dy 0 0; dy 0 0, dy 1 (-2)]
  E := zeroBox 2

/-- `ρ = 1/2`, `≈` within `1/8`, and fuel for forty rounds of either loop. -/
def ρr : D := dy 1 (-1)

def tolr : D := dy 1 (-3)

def fuelr : ℕ := 40

/-- Line 5's look-ahead box at the hidden layer, and the neurons line 6 merges there. -/
def lookAhead : Interval (Vec D 4) :=
  (Layer.activation (S := fun n => Interval (Vec D n)) (reluRelaxation reluSlope)).enclose
    ((ReducedLinear.toLayer (S := fun n => Interval (Vec D n)) ⟨Wr₁, br₁, zeroBox 4⟩).enclose
      Xr.interval)

def mergedLine : String :=
  match bucketTolerance FloatOps.le tolr fuelr (.static [dy 0 0]) lookAhead ρr with
  | none => "Alg. 1 ran out of fuel"
  | some B => "merged by Alg. 1: neurons " ++
      String.intercalate ", " ((List.finRange 4).filterMap fun i =>
        if B i then some (toString (i.val + 1)) else none)

/-- The layer widths of a network in [1, Eq. 2]'s form. -/
def widths : {n m : ℕ} → ReducibleNetwork D n m → List ℕ
  | n, _, .nil => [n]
  | n, _, .cons _ _ _ _ rest => n :: widths rest

/-- The error box each linear layer carries, one line per layer. -/
def errorLines : {n m : ℕ} → ReducibleNetwork D n m → ℕ → List String
  | _, _, .nil, _ => []
  | _, _, .cons L _ _ _ rest, k => ("  layer " ++ toString k ++ "  " ++ showBox L.I') ::
      errorLines rest (k + 2)


-- =====================================  MAIN DEFINITION  ====================================== --

def reduceReport : String :=
  let header := [
    "== reduceOnTheFly (network reduction, Alg. 2) at Dyadic 24 ==",
    "",
    "affine 2 -> 4, ReLU, affine 4 -> 2, ReLU; merge buckets static at 0",
    "X = [1, 2] x [0, 0.5], rho = 0.5, |n^/n - rho| <= 0.125",
    "",
    "look-ahead I_2  " ++ showBox lookAhead,
    mergedLine,
    ""]
  -- run Alg. 2, then print the widths, the error boxes and both enclosures
  match reduceOnTheFly (S := fun k => Zonotope (Vec D k)) FloatOps.le tolr fuelr Xr ρr
    reducible with
  | none => String.intercalate "\n" (header ++ ["Alg. 2 ran out of fuel"])
  | some (Φhat, Y) => String.intercalate "\n" (header ++ [
      "widths  " ++ toString (widths reducible) ++ " -> " ++ toString (widths Φhat),
      "error box I' of each reduced linear layer:"] ++ errorLines Φhat 1 ++ [
      "",
      "unreduced enclose  "
        ++ showBox ((reducible.toNetwork (S := fun k => Zonotope (Vec D k))).enclose Xr).interval,
      "reduced Y          " ++ showBox Y.interval])

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
