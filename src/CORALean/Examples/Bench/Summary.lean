import CORALean.Examples.Bench.FloatPrint
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# Per-run summary statistics, so a run's JSON answers without post-processing

Four numbers per dimension, over a run's `Array (Zonotope 𝕋 2)`: the error
box's final and worst-over-steps radius `(E.sup - E.inf) / 2`, the final
nominal hull's half-width `Σ_j |G_ij|` doubled into a width, and the final
total width once `E` is added back on both sides. Beside them, for the
time-point sets a precision ablation cares about: the first step whose
(max-over-dim) error radius exceeds the nominal half-width at that step -- the
set is then mostly error -- and the first step whose error radius exceeds `1`,
a blow-up marker. Both are `none` if the run never crosses either line.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(E.sup - E.inf) / 2` at dimension `i` -- the box's radius, half of
`Output.csvRow`'s full-width `Eradius` column. -/
def aux_eRadius (toD : 𝕋 → Float) (Z : Zonotope 𝕋 2) (i : Fin 2) : Float :=
  (toD (Z.E.sup i) - toD (Z.E.inf i)) / 2.0

/-- `Σ_j |G_ij|` at dimension `i` -- the nominal hull's half-width, CORA's own
formula halved. -/
def aux_nominalHalfWidth (toD : 𝕋 → Float) (Z : Zonotope 𝕋 2) (i : Fin 2) : Float :=
  (Array.ofFn fun j => (toD (Z.G i j)).abs).foldl (· + ·) 0.0

/-- The larger of the two dimensions' values of `f`, `0.0` on an empty run. -/
def aux_maxOverDims (f : Zonotope 𝕋 2 → Fin 2 → Float) (Z : Zonotope 𝕋 2) : Float :=
  let v0 := f Z 0
  let v1 := f Z 1
  if v0 < v1 then v1 else v0

/-- The first index `i < steps.size` at which `p steps[i]` holds, `none` if it
never does -- `Array.findIdx?`, named for what this file uses it for. -/
def aux_firstIndexWhere (p : Zonotope 𝕋 2 → Bool) (steps : Array (Zonotope 𝕋 2)) :
    Option ℕ :=
  steps.findIdx? p

/-- `x` is `NaN` or `±Inf` -- IEEE `>`/`<` never holds against either, which
otherwise hides a genuine blow-up once both sides of a comparison saturate. -/
def aux_notFinite (x : Float) : Bool := x.isNaN || x.isInf

/-- A step is error-dominant once `e`/`w` (its own max-over-dim error radius
and nominal half-width) makes the comparison meaningless (either non-finite)
or `e` genuinely exceeds `w` -- never `false` just because both saturated. -/
def aux_isDominant (e w : Float) : Bool := decide (e > w) || aux_notFinite e || aux_notFinite w

/-- A step is a blow-up once its own max-over-dim error radius `e` is
non-finite or genuinely exceeds `1`. -/
def aux_isBlowup (e : Float) : Bool := decide (e > 1.0) || aux_notFinite e

-- Regression for the IEEE-`>`-never-holds trap above (`9.0 / 0.0`/`0.0 / 0.0` are `Inf`/`NaN`).
#guard aux_isDominant (9.0 / 0.0) (9.0 / 0.0) = true
#guard aux_isDominant (0.0 / 0.0) 1.0 = true
#guard aux_isDominant 1.0 (9.0 / 0.0) = true
#guard aux_isDominant 1.0 (0.0 / 0.0) = true
#guard aux_isDominant 2.0 1.0 = true
#guard aux_isDominant 1.0 2.0 = false
#guard aux_isBlowup (9.0 / 0.0) = true
#guard aux_isBlowup (0.0 / 0.0) = true
#guard aux_isBlowup 2.0 = true
#guard aux_isBlowup 0.5 = false


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One run's summary, over its own `steps` -- final/max error radius, final
nominal and total hull width, and the first step the error dominates or
blows up past `1`. `null`/`{"empty": true}` on an empty run. -/
def summaryJson (toD : 𝕋 → Float) (steps : Array (Zonotope 𝕋 2)) : Json :=
  match steps.back? with
  | none => Json.mkObj [("empty", Json.bool true)]
  | some last =>
    -- per dimension: the error box's radius, and the nominal hull's half-width
    let finalR := Array.ofFn (aux_eRadius toD last)
    let maxR := Array.ofFn fun i => steps.foldl (fun acc Z => max acc (aux_eRadius toD Z i)) 0.0
    let finalHalfW := Array.ofFn (aux_nominalHalfWidth toD last)
    let finalWidth := Array.ofFn fun (i : Fin 2) => 2.0 * finalHalfW[i]!
    let finalTotalWidth := Array.ofFn fun (i : Fin 2) => finalWidth[i]! + 2.0 * finalR[i]!
    -- the two step-index markers, `none` if `steps` never crosses either line
    let dominant := aux_firstIndexWhere
      (fun Z => aux_isDominant (aux_maxOverDims (aux_eRadius toD) Z)
        (aux_maxOverDims (aux_nominalHalfWidth toD) Z))
      steps
    let blowup := aux_firstIndexWhere
      (fun Z => aux_isBlowup (aux_maxOverDims (aux_eRadius toD) Z)) steps
    Json.mkObj
      [ ("finalEradius", Json.arr (finalR.map floatToJson)),
        ("maxEradius", Json.arr (maxR.map floatToJson)),
        ("finalWidth", Json.arr (finalWidth.map floatToJson)),
        ("finalTotalWidth", Json.arr (finalTotalWidth.map floatToJson)),
        ("firstErrorDominantStep",
          match dominant with | some k => Lean.toJson k | none => Json.null),
        ("firstBlowupStep", match blowup with | some k => Lean.toJson k | none => Json.null) ]

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
