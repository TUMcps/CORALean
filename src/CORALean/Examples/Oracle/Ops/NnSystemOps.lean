import CORALean.NN.Operations.IntervalChainSensitivityFloat
import CORALean.NN.Theorems.IntervalChainSensitivityFloatEqImpl
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.Examples.Oracle.Ops.NnOps
import CORALean.Examples.Oracle.Ops.NnReduceOps
import CORALean.Examples.Oracle.Ops.NnConZonoOps

/-!
# A network as a system, and its explanation: CORA's nonlinearSysDT and explain

A network is CORA.cpp's list of layers `{W, b, activation}` (`relu` or `identity`).
`nonlinearSysDT` is CORA.cpp's `NetworkSystemDT` at a point: `y` of `(W h + b) + u_k`, `C` the
sensitivity at `x` (`IntervalChain.sensitivity_outer`) and per layer `D_k = dy / du_k`, the
sensitivity of the rest at layer `k`'s pre-activation, every later offset an identity layer
`I z + u_j`. `explain` is CORA's method `standard`: the logit differences as a last layer, the
normal form, then one zonotope per trial through `neuralNetwork.evaluate` at CORA's `regression`
lines, a feature freed for good if every logit difference stays at most 0 (`nearest` only).

## Inputs
* `dops` – dtype operations
* `op` – op name, without the prefix
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

open CORALean CORALean.Float FloatOps
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The ReLU's image of a box: `[max(l, 0), max(u, 0)]`. -/
private def aux_reluBox (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨maximum I.inf zero, maximum I.sup zero⟩

/-- The ReLU's derivative over a box, a step that rises: `[l > 0, u > 0]` as `0` or `1`. -/
private def aux_reluSlope (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨if ltStrict zero I.inf then one else zero, if ltStrict zero I.sup then one else zero⟩

/-- The ReLU of a box of vectors, entry by entry. -/
private def aux_reluVec {n : ℕ} (X : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  ⟨fun i => (aux_reluBox ⟨X.inf i, X.sup i⟩).inf, fun i => (aux_reluBox ⟨X.inf i, X.sup i⟩).sup⟩

/-- A layer read at `n` inputs: `W`, `b`, whether its activation is a ReLU. -/
private def aux_layer (dops : DtypeOps 𝕋) (n : ℕ) (layer : Json) :
    Except String (Σ m, Mat 𝕋 m n × Vec 𝕋 m × Bool) := do
  checkFields "layer" layer ["W", "b", "activation"]
  let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
  let b ← parseVecFixed dops.readExact m (← field layer "b")
  let relu ← match ← strField layer "activation" with
    | "relu" => pure true
    | "identity" => pure false
    | a => throw s!"a layer's `activation` must be relu or identity, not `{a}`"
  pure ⟨m, W, b, relu⟩

/-- The offsets of a layer of `m` neurons from `first` on in the stacked `u`. -/
private def aux_slice (u : Array 𝕋) (first m : ℕ) : Vec 𝕋 m := fun i => u.getD (first + i.1) zero

/-- The layers from the one reading `n` inputs on, each followed by its offset as an identity
layer `I z + u_k` (the offsets from `first` on in `u`), as an interval chain. -/
private def aux_offsetChain (dops : DtypeOps 𝕋) (u : Array 𝕋) :
    (n : ℕ) → ℕ → List Json → Except String (Σ k, IntervalChain 𝕋 n k)
  | n, _, [] => pure ⟨n, .nil⟩
  | n, first, layer :: rest => do
    let ⟨m, W, b, relu⟩ ← aux_layer dops n layer
    let ⟨k, tail⟩ ← aux_offsetChain dops u m (first + m) rest
    let after : IntervalChain 𝕋 m k := if relu then .act aux_reluBox aux_reluSlope tail else tail
    pure ⟨k, .linear W b (.linear (diagonalBlock fun _ => one) (aux_slice u first m) after)⟩

/-- The layers from the one reading `n` inputs on, without offsets. -/
private def aux_chain (dops : DtypeOps 𝕋) :
    (n : ℕ) → List Json → Except String (Σ k, IntervalChain 𝕋 n k)
  | n, [] => pure ⟨n, .nil⟩
  | n, layer :: rest => do
    let ⟨m, W, b, relu⟩ ← aux_layer dops n layer
    let ⟨k, tail⟩ ← aux_chain dops m rest
    pure ⟨k, .linear W b (if relu then .act aux_reluBox aux_reluSlope tail else tail)⟩

/-- The output and the blocks `D_k` of the layers from the one reading `n` inputs on, at the box
`h` that enters it: `z = (W h + b) + u_k`, the sensitivity of the rest at `z`, then on. -/
private def aux_system (dops : DtypeOps 𝕋) (u : Array 𝕋) :
    (n : ℕ) → ℕ → List Json → Interval (Vec 𝕋 n) → Except String (Json × List Json)
  | _, _, [], h => pure (printIntervalVec dops.showExact h, [])
  | n, first, layer :: rest, h => do
    let ⟨m, W, b, relu⟩ ← aux_layer dops n layer
    let uk := aux_slice u first m
    -- the pre-activation with the offset, and the rest of the network from it
    let z := Interval.plus (Interval.plus (Interval.mtimes W h) ⟨b, b⟩) ⟨uk, uk⟩
    let ⟨_, tail⟩ ← aux_offsetChain dops u m (first + m) rest
    let sub : IntervalChain 𝕋 m _ := if relu then .act aux_reluBox aux_reluSlope tail else tail
    let block := printIntervalMat dops.showExact (sub.sensitivity z)
    let (y, blocks) ← aux_system dops u m (first + m) rest (if relu then aux_reluVec z else z)
    pure (y, block :: blocks)

/-- `neuralNetwork.nonlinearSysDT`: the output `y`, `C` and the blocks of `D` at `x` and `u`. -/
private def aux_nonlinearSysDT (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  checkFields op req ["layers", "x", "u"]
  let layers := (← arrField req "layers").toList
  let ⟨n, x⟩ ← parseVecDyn dops.readExact (← field req "x")
  let ⟨q, uv⟩ ← parseVecDyn dops.readExact (← field req "u")
  let total ← layers.foldlM (fun s L => do pure (s + (← natField (← field L "b") "rows"))) 0
  if q ≠ total then throw s!"{op}: `u` has one offset per neuron of every layer, {total}"
  let u := Array.ofFn uv
  let (y, blocks) ← aux_system dops u n 0 layers (Interval.point x)
  let ⟨_, c⟩ ← aux_chain dops n layers
  pure [("y", y), ("C", printIntervalMat dops.showExact (c.sensitivity (Interval.point x))),
    ("D", Json.arr blocks.toArray)]

/-- The wire entry of an integer. -/
private def aux_int (z : Int) : Json := Json.str s!"{z}*2^0"

/-- The layer of the logit differences `y_i - y_label` of `m` outputs, in the wire's kinds. -/
private def aux_diffLayer (m label : ℕ) : Json :=
  let W := (List.range m).flatMap fun i => (List.range m).map fun j =>
    aux_int ((if i = j then 1 else 0) - (if j = label then 1 else 0))
  Json.mkObj [("kind", "linear"),
    ("W", Json.mkObj [("rows", Lean.toJson m), ("cols", Lean.toJson m),
      ("data", Json.arr W.toArray)]),
    ("b", Json.mkObj [("rows", Lean.toJson m), ("cols", Lean.toJson 1),
      ("data", Json.arr ((List.replicate m (aux_int 0)).toArray))])]

/-- Whether a wire layer is linear. -/
private def aux_isLinear (L : Json) : Bool := (strField L "kind").toOption = some "linear"

/-- The normal form's layers (boxes, points at `nearest`) back in the wire's kinds, the
activations the original ones `acts` in order (the normal form keeps only their names). -/
private def aux_points (layers : Json) (acts : List Json) : Except String (List Json) := do
  let (out, _) ← (← layers.getArr?).toList.foldlM (fun (out, acts) L => do
    if aux_isLinear L then
      pure (out ++ [Json.mkObj [("kind", "linear"), ("W", ← field (← field L "W") "inf"),
        ("b", ← field (← field L "b") "inf")]], acts)
    else pure (out ++ [acts.headD L], acts.tail)) ([], acts)
  pure out

/-- The zonotope of `x` with the features moved by `ε`, one generator each. -/
private def aux_inputSet {n : ℕ} (x : Vec 𝕋 n) (ε : 𝕋) (features : List ℕ) : Zonotope (Vec 𝕋 n) :=
  ⟨features.length, x, fun l i => if features.getD l.1 0 = i.1 then ε else zero,
    ⟨fun _ => zero, fun _ => zero⟩⟩

/-- The zonotope without its last `m` generators (the zero ones of a linear layer's bias). -/
private def aux_dropLast {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) (m : ℕ) : Zonotope (Vec 𝕋 n) :=
  ⟨Z.h - m, Z.c, fun l => Z.G ⟨l.1, by omega⟩, Z.I_error⟩

/-- The layers on the zonotope at CORA's regression lines, the bias generators dropped. -/
private def aux_evaluate (dops : DtypeOps 𝕋) (layers : List Json) {n : ℕ}
    (X : Zonotope (Vec 𝕋 n)) : Except String (Σ k, Zonotope (Vec 𝕋 k)) :=
  layers.foldlM (fun (s : Σ k, Zonotope (Vec 𝕋 k)) L => do
    let req := Json.mkObj [("layers", Json.arr #[L]), ("poly_method", "regression"),
      ("regression_error", "extremum")]
    let ⟨k, Y⟩ ← networkOnZonotope dops "explain" req s.1 s.2
    if (← strField L "kind") = "linear" then pure ⟨k, aux_dropLast Y k⟩ else pure ⟨k, Y⟩)
    ⟨n, X⟩

/-- Whether the output set meets the specification: every logit difference at most 0, or, for one
output, the radius at most `δ`. -/
private def aux_holds {k : ℕ} (Y : Zonotope (Vec 𝕋 k)) (δ : 𝕋) : Bool :=
  let I := Y.interval
  if hk : k = 1 then
    let i : Fin k := ⟨0, by omega⟩
    le (divUp (subUp (I.sup i) (I.inf i)) (addUp one one)) δ
  else (List.finRange k).all fun i => le (I.sup i) zero

/-- `neuralNetwork.explain`: the features freed, CORA's method `standard`. -/
private def aux_explain (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  checkFields op req ["layers", "x", "label", "epsilon", "featOrder", "inputSize",
    "outputThreshold"]
  if dops.guaranteed then
    throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the reply decides on \
      rounded values; use dtype `nearest`"
  else pure ()
  -- the point, the radius, the threshold, the label, the order and the image's size
  let layers := (← arrField req "layers").toList
  let ⟨n, x⟩ ← parseVecDyn dops.readExact (← field req "x")
  let ε ← dops.readExact "epsilon" (← scalarField req "epsilon")
  let δ ← match fieldOpt req "outputThreshold" with
    | none => pure zero
    | some _ => do dops.readExact "outputThreshold" (← scalarField req "outputThreshold")
  let label ← natField req "label"
  let order := (← natArrField req "featOrder").toList
  let size ← match fieldOpt req "inputSize" with
    | none => pure none
    | some _ => do
      match (← natArrField req "inputSize").toList with
      | [C, H, W] =>
        if C * H * W = n then pure (some (C, H * W))
        else throw s!"{op}: the input size [C, H, W] must have the network's {n} inputs"
      | _ => throw s!"{op}: `inputSize` is [C, H, W]"
  -- the outputs: the rows of the last linear layer
  let m ← match (layers.filter aux_isLinear).getLast? with
    | some L => natField (← field L "W") "rows"
    | none => throw s!"{op}: the network has no linear layer"
  if m > 1 ∧ label ≥ m then throw s!"{op}: the label must be a class below {m}"
  -- the logit differences as the last layer, the network in normal form
  let withDiff := if m > 1 then layers ++ [aux_diffLayer m label] else layers
  let acts := withDiff.filter fun L => !aux_isLinear L
  let named ← withDiff.mapM fun L => do
    if aux_isLinear L then pure L else pure (Json.mkObj [("kind", ← field L "kind")])
  let nf ← normalFormOp dops (Json.mkObj [("layers", Json.arr named.toArray),
    ("n", Lean.toJson n)])
  let net ← aux_points (← match nf.lookup "layers" with
    | some j => pure j
    | none => throw s!"{op}: the normal form has no layers") acts
  -- the features of the pixels, every channel of a pixel
  let features (pixels : List ℕ) : List ℕ := match size with
    | none => pixels
    | some (C, hw) => (List.range C).flatMap fun c => pixels.map (c * hw + ·)
  let verified (pixels : List ℕ) : Except String Bool := do
    let ⟨_, Y⟩ ← aux_evaluate dops net (aux_inputSet x ε (features pixels))
    pure (aux_holds Y δ)
  -- all at once, or one by one in the order
  if ← verified order then return [("freed", Lean.toJson order)]
  let freed ← order.foldlM (fun freed f => do
    let trial := freed ++ [f]
    pure (if ← verified trial then trial else freed)) []
  pure [("freed", Lean.toJson freed)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `neuralNetwork.` from this file, run; `none` for a name it does not serve. -/
@[noinline, nospecialize]
def handleNnSystemOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "nonlinearSysDT" => some (aux_nonlinearSysDT dops op req)
  | "explain" => some (aux_explain dops op req)
  | "computeReducedNetwork" => some (computeReducedNetworkOp dops req)
  | "evaluateConZonotope" => some (evaluateConZonotopeOp dops req)
  | _ => none

/-- Every op of `neuralNetwork.` this file serves, without the prefix. -/
def nnSystemOpNames : List String := [ "nonlinearSysDT", "explain", "computeReducedNetwork",
  "evaluateConZonotope" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
