import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Operations.SigmoidRegression
import CORALean.NN.Layers.Operations.SigmoidRegressionExact
import CORALean.NN.Layers.Operations.TanhRegression
import CORALean.NN.Layers.Operations.TanhRegressionExact
import CORALean.NN.Layers.Operations.PolyBoxIndep
import CORALean.NN.Layers.Operations.SigmoidSingh
import CORALean.NN.Layers.Operations.TanhSingh
import CORALean.NN.Layers.Operations.Tanh
import CORALean.NN.Layers.Operations.LeakyRelu
import CORALean.NN.Layers.Operations.Linear
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The network ops: CORA's `nnLayer` and `neuralNetwork` evaluation on a set

`nnLayer.evaluateZonotope` and `nnLayer.evaluatePolyZonotope` apply one layer to a zonotope or a
polynomial zonotope, `neuralNetwork.evaluate` a list of layers to either: `linear` (`W`, `b`),
`relu`, `leakyRelu` (`alpha`), `sigmoid` and `tanh` (`k`). `poly_method` is `singh` (CORA's
`'singh'`, the default), `regression` (CORA's `'regression'`, with a sound error) or `curvature`
(CORALean's tighter one). `regression_error` of `regression` is `bracket` (the default) or
`extremum` (CORA's exact error). `errorForm` of a polynomial zonotope is `box` (the default) or
`GI` (CORA's `add_approx_error_to_GI`). The order of operations is in
`experiments/oracle/README.md`.

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The relaxation of sigmoid and tanh the request asks for. -/
private inductive PolyMethod where
  | singh | curvature | regression | regressionExtremum
  deriving DecidableEq

/-- One layer of the request on a set of the family `S`, of dimension `n`; the set of the new
dimension. `method` picks the relaxation for sigmoid and tanh. -/
private def aux_runLayer (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (method : PolyMethod) (layer : Json) (s : Σ n, S n) : Except String (Σ n, S n) := do
  let ⟨n, X⟩ := s
  -- the layer by its kind, its weights read at the scalar of the dtype
  match ← strField layer "kind" with
  | "linear" =>
    checkFields "linear" layer ["kind", "W", "b"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    pure ⟨m, (Layer.linear (S := S) W b).enclose X⟩
  | "relu" =>
    checkFields "relu" layer ["kind"]
    pure ⟨n, (Layer.relu (S := S) (n := n)).enclose X⟩
  | "leakyRelu" =>
    checkFields "leakyRelu" layer ["kind", "alpha"]
    let α ← dops.readExact "alpha" (← scalarField layer "alpha")
    pure ⟨n, (Layer.leakyRelu (S := S) (n := n) α).enclose X⟩
  -- the two with the choice of the relaxation
  | "sigmoid" =>
    checkFields "sigmoid" layer ["kind", "k"]
    let k ← natField layer "k"
    pure ⟨n, (match method with
      | .curvature => (Layer.sigmoid (S := S) (n := n) k).enclose X
      | .singh => (Layer.sigmoidSingh (S := S) (n := n) k).enclose X
      | .regression => (Layer.sigmoidRegression (S := S) (n := n) k).enclose X
      | .regressionExtremum => (Layer.sigmoidRegressionExact (S := S) (n := n) k).enclose X)⟩
  | "tanh" =>
    checkFields "tanh" layer ["kind", "k"]
    let k ← natField layer "k"
    pure ⟨n, (match method with
      | .curvature => (Layer.tanh (S := S) (n := n) k).enclose X
      | .singh => (Layer.tanhSingh (S := S) (n := n) k).enclose X
      | .regression => (Layer.tanhRegression (S := S) (n := n) k).enclose X
      | .regressionExtremum => (Layer.tanhRegressionExact (S := S) (n := n) k).enclose X)⟩
  | k => throw s!"a layer's `kind` must be linear, relu, leakyRelu, sigmoid or tanh, not `{k}`"

/-- The layers of the list, in order, on the set. -/
private def aux_runLayers (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (method : PolyMethod) (layers : List Json) (s : Σ n, S n) : Except String (Σ n, S n) :=
  layers.foldlM (fun s l => aux_runLayer dops method l s) s

/-- The layers on a polynomial zonotope; with `gi`, CORA's `add_approx_error_to_GI`: the box of a
layer goes to the independent generators. -/
private def aux_runPoly (dops : DtypeOps 𝕋) (method : PolyMethod) (gi : Bool) (layers : List Json)
    (s : Σ n, 𝒫𝒵[𝕋] n) : Except String (Σ n, 𝒫𝒵[𝕋] n) :=
  if gi then
    letI : OfInterval 𝒫𝒵[𝕋] 𝕋 := OfInterval.polyIndep
    aux_runLayers dops (S := 𝒫𝒵[𝕋]) method layers s
  else aux_runLayers dops (S := 𝒫𝒵[𝕋]) method layers s

/-- The layers on the zonotope `Z` or the polynomial zonotope `P` of the request, the output set
under the same key. `gi` puts the error of a layer into the independent generators of `P`. -/
private def aux_run (dops : DtypeOps 𝕋) (name : String) (req : Json) (method : PolyMethod)
    (gi : Bool) (layers : List Json) : Resp := do
  match fieldOpt req "Z", fieldOpt req "P" with
  | some zj, none =>
    if fieldOpt req "errorForm" |>.isSome then
      throw s!"{name}: `errorForm` is for a polynomial zonotope, a zonotope has no error box"
    let dz ← parseZonotope dops.readExact zj
    let ⟨_, Y⟩ ← aux_runLayers dops (S := 𝒵[𝕋]) method layers ⟨dz.n, dz.Z⟩
    pure [("Z", printZonotope dops.showExact Y)]
  | none, some pj =>
    let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field pj "c")
    let P ← parsePolyZonotopeFixed dops.readExact n pj
    let ⟨_, Y⟩ ← aux_runPoly dops method gi layers ⟨n, P⟩
    pure [("P", printPolyZonotope dops.showExact Y)]
  | _, _ => throw s!"{name}: needs exactly one of `Z` (a zonotope) and `P` (a polynomial zonotope)"

/-- The `poly_method`: `singh` (or none), `curvature` or `regression`, the last with its
`regression_error`: `bracket` (or none) or `extremum`, which only `regression` takes. -/
private def aux_method (name : String) (req : Json) : Except String PolyMethod := do
  let err := (fieldOpt req "regression_error").bind (·.getStr?.toOption)
  if (fieldOpt req "regression_error").isSome && err.isNone then
    throw s!"{name}: `regression_error` must be a string"
  match (fieldOpt req "poly_method").bind (·.getStr?.toOption), err with
  | some "regression", none | some "regression", some "bracket" => pure .regression
  | some "regression", some "extremum" => pure .regressionExtremum
  | some "regression", some e =>
    throw s!"{name}: `regression_error` must be bracket or extremum, not `{e}`"
  | _, some _ => throw s!"{name}: `regression_error` is for `poly_method` regression"
  | none, none | some "singh", none => pure .singh
  | some "curvature", none => pure .curvature
  | some m, none =>
    throw s!"{name}: `poly_method` must be singh, regression or curvature, not `{m}`"

/-- The `errorForm`: `true` for `GI`, `false` for `box` or none. -/
private def aux_errorForm (name : String) (req : Json) : Except String Bool :=
  match (fieldOpt req "errorForm").bind (·.getStr?.toOption) with
  | none | some "box" => pure false
  | some "GI" => pure true
  | some m => throw s!"{name}: `errorForm` must be box or GI, not `{m}`"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op of `nnLayer.`, without the prefix. -/
def nnLayerOpNames : List String := [ "evaluateZonotope", "evaluatePolyZonotope" ]

/-- Every op of `neuralNetwork.`, without the prefix. -/
def neuralNetworkOpNames : List String := [ "evaluate" ]

/-- `op` of `nnLayer.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNnLayerOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "evaluateZonotope" | "evaluatePolyZonotope" => some (do
    checkFields op req ["layer", "Z", "P", "poly_method", "regression_error", "errorForm"]
    aux_run dops op req (← aux_method op req) (← aux_errorForm op req) [← field req "layer"])
  | _ => none

/-- `op` of `neuralNetwork.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNeuralNetworkOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "evaluate" => some (do
    checkFields op req ["layers", "Z", "P", "poly_method", "regression_error", "errorForm"]
    aux_run dops op req (← aux_method op req) (← aux_errorForm op req)
      (← arrField req "layers").toList)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
