import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.Sigmoid
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
`relu`, `leakyRelu` (`alpha`), `sigmoid` and `tanh` (`k`). `poly_method` is `singh` (CORA's, the
default) or `curvature` (CORALean's tighter one); `regression` is refused. The order of operations
is in `experiments/oracle/README.md`.

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

/-- One layer of the request on a set of the family `S`, of dimension `n`; the set of the new
dimension. `curv` picks the curvature relaxation for sigmoid and tanh. -/
private def aux_runLayer (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (curv : Bool) (layer : Json) (s : Σ n, S n) : Except String (Σ n, S n) := do
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
    pure ⟨n, (if curv then (Layer.sigmoid (S := S) (n := n) k).enclose X
      else (Layer.sigmoidSingh (S := S) (n := n) k).enclose X)⟩
  | "tanh" =>
    checkFields "tanh" layer ["kind", "k"]
    let k ← natField layer "k"
    pure ⟨n, (if curv then (Layer.tanh (S := S) (n := n) k).enclose X
      else (Layer.tanhSingh (S := S) (n := n) k).enclose X)⟩
  | k => throw s!"a layer's `kind` must be linear, relu, leakyRelu, sigmoid or tanh, not `{k}`"

/-- The layers of the list, in order, on the set. -/
private def aux_runLayers (dops : DtypeOps 𝕋) {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]
    (curv : Bool) (layers : List Json) (s : Σ n, S n) : Except String (Σ n, S n) :=
  layers.foldlM (fun s l => aux_runLayer dops curv l s) s

/-- The layers on the zonotope `Z` or the polynomial zonotope `P` of the request, the output set
under the same key. -/
private def aux_run (dops : DtypeOps 𝕋) (name : String) (req : Json) (curv : Bool)
    (layers : List Json) : Resp := do
  match fieldOpt req "Z", fieldOpt req "P" with
  | some zj, none =>
    let dz ← parseZonotope dops.readExact zj
    let ⟨_, Y⟩ ← aux_runLayers dops (S := 𝒵[𝕋]) curv layers ⟨dz.n, dz.Z⟩
    pure [("Z", printZonotope dops.showExact Y)]
  | none, some pj =>
    let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field pj "c")
    let P ← parsePolyZonotopeFixed dops.readExact n pj
    let ⟨_, Y⟩ ← aux_runLayers dops (S := 𝒫𝒵[𝕋]) curv layers ⟨n, P⟩
    pure [("P", printPolyZonotope dops.showExact Y)]
  | _, _ => throw s!"{name}: needs exactly one of `Z` (a zonotope) and `P` (a polynomial zonotope)"

/-- The `poly_method`: `true` for `curvature`, `false` for `singh` or none. -/
private def aux_curvature (name : String) (req : Json) : Except String Bool :=
  match (fieldOpt req "poly_method").bind (·.getStr?.toOption) with
  | none | some "singh" => pure false
  | some "curvature" => pure true
  | some m => throw s!"{name}: `poly_method` must be singh or curvature, not `{m}`"


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
    checkFields op req ["layer", "Z", "P", "poly_method"]
    aux_run dops op req (← aux_curvature op req) [← field req "layer"])
  | _ => none

/-- `op` of `neuralNetwork.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNeuralNetworkOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "evaluate" => some (do
    checkFields op req ["layers", "Z", "P", "poly_method"]
    aux_run dops op req (← aux_curvature op req) (← arrField req "layers").toList)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
