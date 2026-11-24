import CORALean.NN.Operations.HeldChainBackpropFloat
import CORALean.NN.Operations.EvaluateGraph
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The zonotope batch backpropagation: CORA's backpropZonotopeBatch with the slopes held

A network is CORA.cpp's list of layers `{W, b, activation}` (`relu` or `identity`). The forward
pass is `neuralNetwork.evaluateGraph`'s on the chain (CORA.cpp's `ZonoNet::forward`, every
approximation error a generator): `W Z + b`, then the ReLU's line at the bounds of the set
(`reluRelaxation reluSlope`), whose slopes it stores as CORA's `backprop.store.coeffs`. The
backward pass is `Float.HeldChain.backprop` of `W` and the slopes on the gradient of the center and
on that of every input generator (`HeldChain.backprop_outer`); the gradients of the approximation
errors' generators stop at their layer. CORA's `exact_backprop` is not served.

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

/-- The ReLU of CORA.cpp's verify, CORALean's line at the bounds of the set. -/
private def aux_relu : Relaxation 𝕋 := reluRelaxation reluSlope

/-- The slopes the ReLU's lines take at the bounds of `Z` (the forward pass's own). -/
private def aux_slopes {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  let I := Z.interval.materialise
  fun i => (aux_relu (𝕋 := 𝕋)).slope (I.inf i) (I.sup i)

/-- One layer `W`, `b`, `act` on `Z`, as `evaluateGraph` runs it. -/
private def aux_layer {n m : ℕ} (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (act : GraphAct 𝕋 m)
    (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 m) :=
  let L : GraphLayer 𝕋 [n] m := ⟨⟨0, Nat.zero_lt_one⟩, W, b, [], act⟩
  (GraphNet.layer L .done).evaluateGraph Z

/-- The request's `exact` must be absent or false. -/
private def aux_heldOnly (op : String) (req : Json) : Except String Unit :=
  match fieldOpt req "exact" with
  | none | some (.bool false) => pure ()
  | some _ => throw s!"{op}: only `exact` false is served (the lines held, CORA without \
      exact_backprop)"

/-- The input set `Z`, without an error box (CORA.cpp's input is a center and generators). -/
private def aux_inputSet (dops : DtypeOps 𝕋) (op : String) (req : Json) :
    Except String (DynZonotope 𝕋) := do
  let zj ← field req "Z"
  if (fieldOpt zj "E").isSome then throw s!"{op}: `Z` is a center and generators, no `E`"
  parseZonotope dops.readExact zj

/-- The layers from the one reading `n` inputs on, run forward on `Z`: the held chain, each layer's
slopes (`null` without a ReLU) and the output's generator count. -/
private def aux_held (dops : DtypeOps 𝕋) :
    (n : ℕ) → List Json → Zonotope (Vec 𝕋 n) →
      Except String ((Σ k, HeldChain 𝕋 n k) × List Json × ℕ)
  | _, [], Z => pure (⟨_, .nil⟩, [], Z.h)
  | n, layer :: rest, Z => do
    checkFields "layer" layer ["W", "b", "activation"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    -- the linear layer, as evaluateGraph's
    let Z₁ := aux_layer W b .identity Z
    match ← strField layer "activation" with
    | "identity" =>
      let (⟨k, tail⟩, ss, q) ← aux_held dops m rest Z₁
      pure (⟨k, .linear W tail⟩, Json.null :: ss, q)
    | "relu" =>
      -- the slopes at the set's bounds, then the activation's set with its error generators
      let s := aux_slopes Z₁
      let Z₂ := aux_layer W b (.elementwise aux_relu true) Z
      let (⟨k, tail⟩, ss, q) ← aux_held dops m rest Z₂
      pure (⟨k, .linear W (.slope s tail)⟩, printVec dops.showExact s :: ss, q)
    | a => throw s!"a layer's `activation` must be relu or identity, not `{a}`"

/-- The gradients at the input of `H`: the center's, and the first `h` generators' of the
gradient `gG` (`k × q`, one column per generator of the output). -/
private def aux_reply (dops : DtypeOps 𝕋) {n k q : ℕ} (H : HeldChain 𝕋 n k) (h : ℕ)
    (gc : Vec 𝕋 k) (gG : Mat 𝕋 k q) : Resp := do
  if hq : h ≤ q then
    let c := H.backprop (Interval.point gc)
    let cols := Array.ofFn fun j : Fin h =>
      H.backprop (Interval.point fun i => gG i ⟨j.1, lt_of_lt_of_le j.2 hq⟩)
    let get := fun (j : Fin h) => cols.getD j.1 (Interval.point fun _ => FloatOps.zero)
    let G : Interval (Mat 𝕋 n h) := ⟨fun i j => (get j).inf i, fun i j => (get j).sup i⟩
    pure [("gc", printIntervalVec dops.showExact c), ("gG", printIntervalMat dops.showExact G)]
  else throw s!"`gG` has {q} columns, fewer than the input's {h} generators"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `neuralNetwork.backpropZonotopeBatch`: the gradients at the input set's center and generators,
the forward pass's slopes beside them. -/
def backpropZonotopeBatchOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "backpropZonotopeBatch"
  checkFields op req ["layers", "Z", "gc", "gG", "exact"]
  aux_heldOnly op req
  let dz ← aux_inputSet dops op req
  let (⟨k, H⟩, slopes, q) ← aux_held dops dz.n (← arrField req "layers").toList dz.Z
  let gc ← parseVecFixed dops.readExact k (← field req "gc")
  let ⟨q', gG⟩ ← parseMatRowsFixed dops.readExact k (← field req "gG")
  if q' ≠ q then throw s!"{op}: `gG` has one column per generator of the output, {q}, not {q'}"
  let reply ← aux_reply dops H dz.Z.h gc gG
  pure (reply ++ [("slopes", Json.arr slopes.toArray)])

/-- `nnLayer.backpropZonotopeBatch`: a `linear` layer's `W' gc`, `W' gG`, or a `relu` layer's
`m .* gc`, `m .* gG` at the first generators, the slopes `m` at the bounds of its input set `Z`. -/
def backpropZonotopeBatchLayerOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "backpropZonotopeBatch"
  checkFields op req ["layer", "Z", "gc", "gG", "exact"]
  aux_heldOnly op req
  let layer ← field req "layer"
  match ← strField layer "kind" with
  -- a linear layer maps the gradients by `W'`, a ReLU scales them by its slopes
  | "linear" =>
    checkFields op layer ["kind", "W", "b"]
    let d ← parseMatDyn dops.readExact (← field layer "W")
    let gc ← parseVecFixed dops.readExact d.r (← field req "gc")
    let ⟨q, gG⟩ ← parseMatRowsFixed dops.readExact d.r (← field req "gG")
    aux_reply dops (.linear d.M .nil) q gc gG
  | "relu" =>
    checkFields op layer ["kind"]
    let dz ← aux_inputSet dops op req
    let gc ← parseVecFixed dops.readExact dz.n (← field req "gc")
    let ⟨_, gG⟩ ← parseMatRowsFixed dops.readExact dz.n (← field req "gG")
    let s := aux_slopes dz.Z
    let reply ← aux_reply dops (.slope s .nil) dz.Z.h gc gG
    pure (reply ++ [("slopes", Json.arr #[printVec dops.showExact s])])
  | k => throw s!"{op}: the layer's `kind` must be linear or relu, not `{k}`"

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
