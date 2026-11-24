import CORALean.NN.Layers.Operations.SoundLayerActivationTaylmFit
import CORALean.NN.Layers.Operations.SoundLayerAffineTaylm
import CORALean.NN.Layers.Theorems.ReluSinghQuadRelaxationEncloses
import CORALean.NN.Layers.Theorems.PadToEncloses
import CORALean.NN.Layers.Theorems.ReluRelaxationEncloses
import CORALean.NN.Layers.Theorems.SigmoidSinghRelaxationEncloses
import CORALean.NN.Layers.Theorems.SigmoidRegressionRelaxationEncloses
import CORALean.NN.Layers.Theorems.SigmoidRegressionExactRelaxationEncloses
import CORALean.NN.Layers.Theorems.TanhSinghRelaxationEncloses
import CORALean.NN.Layers.Theorems.TanhRegressionRelaxationEncloses
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The op `neuralNetwork.evaluateTaylm`: a network on Taylor models

CORA.cpp's `NeuralNetwork::evaluate_taylm`: the layers as `SoundLayer.affineTaylm` and
`SoundLayer.activationTaylmFit` applied in turn, each with its proved enclosure, so the chain
encloses the network (`NeuralNetwork.enclose_outer` of the same layers). An activation's neurons
take CORALean's line (order 1, the line of `neuralNetwork.evaluate` at the `poly_method`) or, for
`relu` at `singh`, the parabola of order 2 (`reluSinghQuadRelaxation`). `order` is a number or
one per neuron, as CORA.cpp's `aux_orders` reads it. The input models are `x`, each in the `T`
form of `taylm.*`.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* the output models, `Y`
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Float.SoundFloatArithmetic
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The line of each kind CORA.cpp's `aux_line` takes, as `neuralNetwork.evaluate` serves it:
`regression` picks the least-squares line (and `extremum` its exact error, for the sigmoid), else
Singh's; with its activation, held `Erased`, and its theorem. -/
private def aux_line (method : String) (layer : Json) :
    Except String (Σ' (R : Relaxation 𝕋) (σ : Erased (ℝ → ℝ)), R.Encloses σ.out) := do
  match ← strField layer "kind" with
  | "relu" => pure ⟨reluRelaxation reluSlope, Erased.mk Real.relu,
      by rw [Erased.out_mk]; exact reluRelaxation_encloses reluSlope⟩
  | "sigmoid" =>
    let k ← natField layer "k"
    match method with
    | "regression" => pure ⟨_, Erased.mk Real.sigmoid,
        by rw [Erased.out_mk]; exact sigmoidRegressionRelaxation_encloses k⟩
    | "extremum" => pure ⟨_, Erased.mk Real.sigmoid,
        by rw [Erased.out_mk]; exact sigmoidRegressionExactRelaxation_encloses k⟩
    | _ => pure ⟨_, Erased.mk Real.sigmoid,
        by rw [Erased.out_mk]; exact sigmoidSinghRelaxation_encloses k⟩
  -- the tanh as the sigmoid at twice the argument; its exact-error line is not served here
  | "tanh" =>
    let k ← natField layer "k"
    match method with
    | "regression" => pure ⟨_, Erased.mk Real.tanh,
        by rw [Erased.out_mk]; exact tanhRegressionRelaxation_encloses k⟩
    | "extremum" => throw "evaluateTaylm: tanh at `regression_error` extremum is not served"
    | _ => pure ⟨_, Erased.mk Real.tanh,
        by rw [Erased.out_mk]; exact tanhSinghRelaxation_encloses k⟩
  | kind => throw s!"evaluateTaylm: a layer's `kind` must be linear, relu, sigmoid or tanh, not \
      `{kind}`"

/-- Every neuron's order, CORA.cpp's `aux_orders`: none is 1, one value is every neuron's, `n`
values are one per neuron, any other count takes the largest. -/
private def aux_orders (layer : Json) (n : ℕ) : Except String (Fin n → ℕ) := do
  match fieldOpt layer "order" with
  | none => pure fun _ => 1
  | some j =>
    match j.getNat? with
    | .ok k => pure fun _ => k
    | .error _ =>
      let a ← natArrField layer "order"
      if a.isEmpty then pure fun _ => 1
      else if h : a.size = n then pure fun i => a[i.val]'(h ▸ i.isLt)
      else pure fun _ => a.foldl max 0

/-- The activation layer of `layer` on `n` neurons: the line where every order is 1, else (ReLU
at `singh` only) the parabola where the order is 2 and the line padded to degree 2 elsewhere. -/
private def aux_activation (method : String) (layer : Json) (n d : ℕ) :
    Except String (SoundLayer (TaylmArray 𝕋 d) n n) := do
  let ⟨R, σ, hR⟩ ← aux_line method layer
  let o ← aux_orders layer n
  if (List.finRange n).all fun i => o i ≤ 1 then
    pure (SoundLayer.activationTaylmFit (fun _ => R.toPoly) (fun _ _ _ => 1) σ
      (fun _ => Relaxation.toPoly_encloses hR) fun _ _ _ k hk => absurd hk (by omega))
  else if (← strField layer "kind") = "relu" && method = "singh" &&
      (List.finRange n).all fun i => o i ≤ 2 then
    let line := (reluRelaxation (𝕋 := 𝕋) reluSlope).toPoly.padTo 2
    let P : LayerRelaxation 𝕋 n 2 := fun i => if o i = 2 then reluSinghQuadRelaxation else line
    -- degree 2 unless the coefficient of x² is certified zero (the linear boxes, the lines)
    let top : Fin n → 𝕋 → 𝕋 → ℕ := fun i l u =>
      if FloatOps.le ((P i).coeffs l u 2) FloatOps.zero &&
          FloatOps.le FloatOps.zero ((P i).coeffs l u 2) then 1 else 2
    pure (SoundLayer.activationTaylmFit P top (Erased.mk Real.relu)
      (fun i => by
        simp only [P, Erased.out_mk]
        split
        · exact reluSinghQuadRelaxation_encloses
        · exact PolyRelaxation.padTo_encloses (by norm_num)
            (Relaxation.toPoly_encloses (reluRelaxation_encloses reluSlope)))
      -- a power above `top` has a zero coefficient
      fun i l u k hk => by
        simp only [top] at hk
        split_ifs at hk with hc
        · have hk1 : k.succ = 2 := by ext; simp; omega
          rw [hk1]
          simp only [Bool.and_eq_true] at hc
          exact le_antisymm (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le hc.1)
            (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le hc.2)
        · have := k.isLt; omega)
  else throw "evaluateTaylm: order 2 is served for relu at poly_method singh, every other \
      neuron at order 1"

/-- The layers of `layers` in turn on the models `X`, each a `SoundLayer`: the output models. -/
private def aux_run (dops : DtypeOps 𝕋) (method : String) (d : ℕ) :
    List Json → (Σ n, TaylmArray 𝕋 d n) → Except String (Σ m, TaylmArray 𝕋 d m)
  | [], X => pure X
  | layer :: rest, ⟨n, X⟩ => do
    if (← strField layer "kind") = "linear" then
      checkFields "linear" layer ["kind", "W", "b"]
      match n, X with
      | 0, _ => throw "evaluateTaylm: a linear layer needs at least one input"
      | n' + 1, X =>
        let ⟨m, W⟩ ← parseMatColsFixed dops.readExact (n' + 1) (← field layer "W")
        let b ← parseVecFixed dops.readExact m (← field layer "b")
        aux_run dops method d rest ⟨m, (SoundLayer.affineTaylm (d := d) W b).enclose X⟩
    else
      checkFields "activation" layer ["kind", "k", "order"]
      let L ← aux_activation (𝕋 := 𝕋) method layer n d
      aux_run dops method d rest ⟨n, L.enclose X⟩

/-- The model `j` of `d` variables, as `taylm.*` reads it. -/
private def aux_parseModel (dops : DtypeOps 𝕋) (d : ℕ) (j : Json) : Except String (Taylm 𝕋 d) := do
  if (← natField j "vars") ≠ d then throw "evaluateTaylm: the models must share their variables"
  let terms ← (← arrField j "terms").toList.mapM fun t => do
    let c ← dops.readExact "c" (← scalarField t "c")
    let e ← natArrField t "e"
    if h : e.size = d then pure (c, fun k : Fin d => e[k.val]'(h ▸ k.isLt))
    else throw s!"a term has {e.size} exponents, the model {d} variables"
  let R ← field j "rem"
  pure ⟨terms, ⟨← dops.readExact "rem" (← scalarField R "inf"),
    ← dops.readExact "rem" (← scalarField R "sup")⟩, ⟨FloatOps.zero, FloatOps.zero⟩,
    ← natField j "maxOrder"⟩

/-- A model in the `T` form of `taylm.*`. -/
private def aux_printModel (dops : DtypeOps 𝕋) {d : ℕ} (T : Taylm 𝕋 d) : Json :=
  let s := fun x : 𝕋 => Json.str (dops.showExact x)
  let I := fun J : Interval 𝕋 => Json.mkObj [("inf", s J.inf), ("sup", s J.sup)]
  Json.mkObj [("vars", Lean.toJson d), ("maxOrder", Lean.toJson T.maxOrder),
    ("terms", Json.arr (T.terms.toArray.map fun a => Json.mkObj
      [("c", s a.1), ("e", Lean.toJson (Array.ofFn a.2))])),
    ("rem", I T.rem), ("Ierr", I T.I_error)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The network of `layers` on the models `x`: the output models. -/
def evaluateTaylmOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "evaluateTaylm" req ["layers", "x", "poly_method", "regression_error"]
  let method ← match (fieldOpt req "poly_method").bind (·.getStr?.toOption),
      (fieldOpt req "regression_error").bind (·.getStr?.toOption) with
    | none, none | some "singh", none => pure "singh"
    | some "regression", none | some "regression", some "bracket" => pure "regression"
    | some "regression", some "extremum" => pure "extremum"
    | _, _ => throw "evaluateTaylm: `poly_method` must be singh or regression (with \
        `regression_error` bracket or extremum)"
  let xs ← arrField req "x"
  let some x₀ := xs[0]? | throw "evaluateTaylm: needs at least one model"
  let d ← natField x₀ "vars"
  let models ← xs.mapM (aux_parseModel dops d)
  let X : TaylmArray 𝕋 d models.size := ⟨fun i => models[i]⟩
  let ⟨_, Y⟩ ← aux_run dops method d (← arrField req "layers").toList ⟨models.size, X⟩
  pure [("Y", Json.arr (Array.ofFn fun i => aux_printModel dops (Y.taylm i)))]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
