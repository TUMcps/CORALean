import CORALean.NN.Operations.IntervalChainFwdFloat
import CORALean.NN.Operations.IntervalChainBackpropFloat
import CORALean.NN.Operations.IntervalChainSensitivityFloat
import CORALean.NN.Operations.FgsmAttackFloat
import CORALean.NN.Operations.SoftmaxLossDer
import CORALean.NN.Operations.InputNeuronOrderFloat
import CORALean.NN.Theorems.IntervalChainFwdFloatEqImpl
import CORALean.NN.Theorems.IntervalChainBackpropFloatEqImpl
import CORALean.NN.Theorems.IntervalChainSensitivityFloatEqImpl
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The bound and gradient passes of a ReLU network: CORA's propagateBounds, backprop, calcSensitivity

A network is CORA.cpp's list of layers `{W, b, activation}` (`relu` or `identity`), read as a
`Float.IntervalChain`: `linear W b`, then the ReLU's box image and derivative. `propagateBounds` is
`IntervalChain.fwd` from layer `i`'s ReLU to the next ReLU, met with the bounds stored there;
`backpropIntervalBatch`, `backprop` (at a point) and `computeFGSMAttack` (CORA's loss
`softmax(y) - t`, `softmaxLossDer`) run `IntervalChain.backprop`; `sensitivity` and
`getInputNeuronOrder` run `IntervalChain.sensitivity`. The theorems are `fwd_outer`,
`backprop_outer`, `sensitivity_outer`, `fgsmAttack_outer` and `getInputNeuronOrder_eq`.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* the op's reply
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The ReLU's image of a box: `[max(l, 0), max(u, 0)]`. -/
private def aux_reluBox (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨FloatOps.maximum I.inf FloatOps.zero, FloatOps.maximum I.sup FloatOps.zero⟩

/-- The ReLU's derivative over a box, a step that rises: `[l > 0, u > 0]` as `0` or `1`. -/
private def aux_reluSlope (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨if FloatOps.ltStrict FloatOps.zero I.inf then FloatOps.one else FloatOps.zero,
    if FloatOps.ltStrict FloatOps.zero I.sup then FloatOps.one else FloatOps.zero⟩

/-- The activation of a layer: whether it is a ReLU (`identity` is none). -/
private def aux_isRelu (layer : Json) : Except String Bool := do
  match (← strField layer "activation") with
  | "relu" => pure true
  | "identity" => pure false
  | a => throw s!"a layer's `activation` must be relu or identity, not `{a}`"

/-- The layers from the one reading `n` inputs on, as an interval chain. -/
private def aux_chain (dops : DtypeOps 𝕋) :
    (n : ℕ) → List Json → Except String (Σ k, IntervalChain 𝕋 n k)
  | n, [] => pure ⟨n, .nil⟩
  | n, layer :: rest => do
    checkFields "layer" layer ["W", "b", "activation"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    let relu ← aux_isRelu layer
    let ⟨k, tail⟩ ← aux_chain dops m rest
    pure ⟨k, .linear W b (if relu then .act aux_reluBox aux_reluSlope tail else tail)⟩

/-- From layer `i`'s ReLU on: its box image, then the linear maps up to and including the first
layer `j > i` with a ReLU, whose index the result names (`none`: no ReLU follows). -/
private def aux_segment (dops : DtypeOps 𝕋) :
    (n : ℕ) → ℕ → List Json → Except String (Option (ℕ × Σ k, IntervalChain 𝕋 n k))
  | _, _, [] => pure none
  | n, j, layer :: rest => do
    checkFields "layer" layer ["W", "b", "activation"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    if ← aux_isRelu layer then pure (some (j, ⟨m, .linear W b .nil⟩))
    else
      match ← aux_segment dops m (j + 1) rest with
      | none => pure none
      | some (j', ⟨k, tail⟩) => pure (some (j', ⟨k, .linear W b tail⟩))

/-- The bounds `{l, u}` of a layer, if they are set (not `null`). -/
private def aux_bounds? (dops : DtypeOps 𝕋) (n : ℕ) (j : Json) :
    Except String (Option (Vec 𝕋 n × Vec 𝕋 n)) :=
  match j with
  | .null => pure none
  | _ => do
    pure (some (← parseVecFixed dops.readExact n (← field j "l"),
      ← parseVecFixed dops.readExact n (← field j "u")))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `neuralNetwork.propagateBounds`: the new bounds of the next ReLU layer after layer `i`. -/
def propagateBoundsOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "propagateBounds" req ["layers", "bounds", "i"]
  let layers := (← arrField req "layers").toList
  let bounds := (← arrField req "bounds")
  let i ← natField req "i"
  if bounds.size ≠ layers.length ∨ i ≥ layers.length then
    throw "propagateBounds: one bound (or null) per layer, and `i` a layer"
  let layer := layers[i]!
  let relu ← aux_isRelu layer
  -- the bounds of layer `i` are of its outputs, as many as its bias
  let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field layer "b")
  let unchanged := pure [("bounds", Json.arr bounds)]
  if !relu then unchanged else
  match ← aux_bounds? dops n bounds[i]! with
  | none => unchanged
  | some (l, u) =>
    match ← aux_segment dops n (i + 1) (layers.drop (i + 1)) with
    | none => unchanged
    | some (j, ⟨k, seg⟩) =>
      -- the ReLU's image of the box, then the maps
      let start : IntervalChain 𝕋 n k := .act aux_reluBox aux_reluSlope seg
      let (lo, hi) := start.fwd (Interval.point l, Interval.point u)
      let lo' := lo.inf
      let hi' := hi.sup
      let met ← match ← aux_bounds? dops k bounds[j]! with
        | none => pure (lo', hi')
        | some (sl, su) => pure (fun r => FloatOps.maximum (lo' r) (sl r),
            fun r => FloatOps.minimum (hi' r) (su r))
      let out := Json.mkObj [("l", printVec dops.showExact met.1),
        ("u", printVec dops.showExact met.2)]
      pure [("bounds", Json.arr (bounds.set! j out))]

/-- `neuralNetwork.backpropIntervalBatch` (`point` false) and `neuralNetwork.backprop` (`point`
true, `x` and `g`): the gradient's bounds at the input. -/
def backpropOp (dops : DtypeOps 𝕋) (point : Bool) (req : Json) : Resp := do
  if point then checkFields "backprop" req ["layers", "x", "g"]
  else checkFields "backpropIntervalBatch" req ["layers", "l", "u", "gl", "gu"]
  let ⟨n, l⟩ ← parseVecDyn dops.readExact (← field req (if point then "x" else "l"))
  let u ← parseVecFixed dops.readExact n (← field req (if point then "x" else "u"))
  let ⟨k, c⟩ ← aux_chain dops n (← arrField req "layers").toList
  let gl ← parseVecFixed dops.readExact k (← field req (if point then "g" else "gl"))
  let gu ← parseVecFixed dops.readExact k (← field req (if point then "g" else "gu"))
  let (G₁, G₂) := c.backprop (Interval.point l, Interval.point u)
    (Interval.point gl, Interval.point gu)
  if point then pure [("g", printIntervalVec dops.showExact ⟨G₁.inf, G₂.sup⟩)]
  else pure [("gl", printIntervalVec dops.showExact G₁), ("gu", printIntervalVec dops.showExact G₂)]

/-- `neuralNetwork.sensitivity`: the Jacobian of the outputs in the inputs at the point `x`. -/
def sensitivityOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "sensitivity" req ["layers", "x"]
  let ⟨n, x⟩ ← parseVecDyn dops.readExact (← field req "x")
  let ⟨_, c⟩ ← aux_chain dops n (← arrField req "layers").toList
  pure [("J", printIntervalMat dops.showExact (c.sensitivity (Interval.point x)))]

/-- `neuralNetwork.computeFGSMAttack`: the point `x` moved by `epsilon` along the sign of the
gradient of CORA's loss `softmax(y) - t` (`k`, the exponential's depth, 10 by default). -/
def fgsmAttackOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "computeFGSMAttack" req ["layers", "x", "t", "epsilon", "k"]
  let ⟨n, x⟩ ← parseVecDyn dops.readExact (← field req "x")
  let ⟨m, c⟩ ← aux_chain dops n (← arrField req "layers").toList
  let t ← parseVecFixed dops.readExact m (← field req "t")
  -- the step and the exponential's depth
  let ε ← dops.readExact "epsilon" (← scalarField req "epsilon")
  let k := (natField req "k").toOption.getD 10
  let z := c.fgsmAttack (Interval.point x) t (Interval.point ε) (softmaxLossDer k)
  pure [("z", printIntervalVec dops.showExact z)]

/-- `neuralNetwork.getInputNeuronOrder`: the pixels (0-based) `in-order`, along CORA.cpp's `snake`
of an `inputSize` `[C, H, W]` image (a pixel is `y W + x`), or by the mean absolute sensitivity at
`x`, the least first (`null` where a sound box cannot rank two). -/
def inputNeuronOrderOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "getInputNeuronOrder"
  checkFields op req ["layers", "method", "x", "inputSize"]
  let layers := (← arrField req "layers").toList
  -- the network's width, from the first layer's `W`
  let n ← match layers with
    | [] => throw s!"{op}: the network has no layer"
    | L :: _ => do pure (← natField (← field L "W") "cols")
  let size ← match fieldOpt req "inputSize" with
    | none => pure none
    | some _ => do
      match (← natArrField req "inputSize").toList with
      | [C, H, W] =>
        if C * H * W = n then pure (some (C, H, W))
        else throw s!"{op}: the input size [C, H, W] must have the network's {n} inputs"
      | _ => throw s!"{op}: `inputSize` is [C, H, W]"
  -- the order of the method
  let out (L : List ℕ) : Resp := pure [("order", Lean.toJson L)]
  match ← strField req "method" with
  | "in-order" => out (List.range (match size with | none => n | some (_, H, W) => H * W))
  | "snake" =>
    match size with
    | none => throw s!"{op}: a snake needs the input size"
    | some (_, H, W) => out (snakeOrder H W fun i j => (i : ℕ) * W + j)
  | "sensitivity" =>
    let x ← parseVecFixed dops.readExact n (← field req "x")
    let ⟨_, c⟩ ← aux_chain dops n layers
    match c.getInputNeuronOrder .sensitivity (Interval.point x)
        (size.map fun (C, H, W) => (H, W, C)) with
    | some L => out L
    | none => pure [("order", Json.null)]
  | m => throw s!"{op}: the method is in-order, snake or sensitivity, not `{m}`"

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
