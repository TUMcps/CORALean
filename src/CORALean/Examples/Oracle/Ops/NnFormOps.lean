import CORALean.NN.Operations.ActivationKindMergeValues
import CORALean.NN.Operations.WeightNetworkNormalFormFloat
import CORALean.NN.Layers.Operations.GroupSortFloat
import CORALean.ContSet.Zonotope.Float.Operations.ReduceShortest
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The network forms: CORA's merge buckets, group sort, normal form and generator reduction

`nnLayer.mergeBuckets` is `ActivationKind.mergeValues` (CORA's `getMergeBuckets`).
`nnLayer.groupSort` is `groupSortFloat` on a point (CORA's `nnGroupSortLayer`).
`nnLayer.generatorReduction` is `Zonotope.reduceShortest` at `maxGens - n` kept generators
(CORA's `nnGeneratorReductionLayer`; `Zonotope.reduceShortest_outer`).
`neuralNetwork.normalForm` is `Float.WeightNetwork.normalForm` (CORA's `getNormalForm`;
`WeightNetwork.normalForm_encloses`): the linear layers between activations fused,
`W_k W` and `W_k b + b_k`, as boxes.

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

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The activation `kind` CORA merges at, by name. -/
private def aux_kind (kind : String) : Except String ActivationKind :=
  match kind with
  | "relu" => pure .relu
  | "sigmoid" => pure .sigmoid
  | "tanh" => pure .tanh
  | k => throw s!"mergeBuckets: `kind` must be relu, sigmoid or tanh, not `{k}`"

/-- The layers of `normalForm` from the one reading `n` inputs on, and each activation's name. -/
private def aux_build (dops : DtypeOps 𝕋) :
    (n : ℕ) → List Json → Except String ((Σ k, WeightNetwork 𝕋 n k) × List String)
  | n, [] => pure (⟨n, .nil⟩, [])
  | n, layer :: rest => do
    match ← strField layer "kind" with
    | "linear" =>
      checkFields "normalForm" layer ["kind", "W", "b"]
      let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
      let b ← parseVecFixed dops.readExact m (← field layer "b")
      let (⟨k, tail⟩, names) ← aux_build dops m rest
      pure (⟨k, .cons (.linear (Interval.point W) (Interval.point b)) tail⟩, names)
    -- the two maps `normalForm` fuses into the linear layers around them
    | "elementwiseAffine" =>
      checkFields "normalForm" layer ["kind", "scale", "offset"]
      let s ← parseVecFixed dops.readExact n (← field layer "scale")
      let o ← parseVecFixed dops.readExact n (← field layer "offset")
      let (⟨k, tail⟩, names) ← aux_build dops n rest
      pure (⟨k, .cons (.elementwiseAffine (Interval.point s) (Interval.point o)) tail⟩, names)
    | "identity" =>
      checkFields "normalForm" layer ["kind"]
      let (⟨k, tail⟩, names) ← aux_build dops n rest
      pure (⟨k, .cons .identity tail⟩, names)
    -- an activation stays where it is: its name is all the reply needs
    | name =>
      checkFields "normalForm" layer ["kind"]
      let (⟨k, tail⟩, names) ← aux_build dops n rest
      pure (⟨k, .cons (.activation id) tail⟩, name :: names)

/-- The fused network as the wire's list, the activations named in order. -/
private def aux_print (dops : DtypeOps 𝕋) :
    {n k : ℕ} → WeightNetwork 𝕋 n k → List String → List Json
  | _, _, .nil, _ => []
  | _, _, .cons (.linear W b) rest, names =>
    Json.mkObj [("kind", "linear"), ("W", printIntervalMat dops.showExact W),
      ("b", printIntervalVec dops.showExact b)] :: aux_print dops rest names
  | _, _, .cons (.elementwiseAffine s o) rest, names =>
    Json.mkObj [("kind", "elementwiseAffine"), ("scale", printIntervalVec dops.showExact s),
      ("offset", printIntervalVec dops.showExact o)] :: aux_print dops rest names
  | _, _, .cons .identity rest, names =>
    Json.mkObj [("kind", "identity")] :: aux_print dops rest names
  | _, _, .cons (.activation _) rest, names =>
    Json.mkObj [("kind", names.headD "activation")] :: aux_print dops rest names.tail


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `nnLayer.` from this file, run; `none` for a name it does not serve. -/
@[noinline, nospecialize]
def handleNnFormLayerOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "mergeBuckets" => some (do
    checkFields op req ["kind"]
    let values := (← aux_kind (← strField req "kind")).mergeValues
    -- the integers as exact scalars of the dtype
    let ⟨_, v⟩ ← parseVecDyn dops.readExact
      (Json.mkObj [("rows", Lean.toJson values.length), ("cols", Lean.toJson 1),
        ("data", Json.arr (values.map fun z => Json.str s!"{z}*2^0").toArray)])
    pure [("buckets", printVec dops.showExact v)])
  | "groupSort" => some (do
    checkFields op req ["groupSize", "x"]
    let g ← natField req "groupSize"
    if g = 0 then throw "groupSort: `groupSize` must be at least 1"
    let ⟨_, x⟩ ← parseVecDyn dops.readExact (← field req "x")
    pure [("y", printVec dops.showExact (groupSortFloat g x))])
  | "generatorReduction" => some (do
    checkFields op req ["maxGens", "Z"]
    let maxGens ← natField req "maxGens"
    let dz ← parseZonotope dops.readExact (← field req "Z")
    if maxGens < dz.n then
      throw s!"generatorReduction: `maxGens` must be at least the dimension {dz.n}"
    pure [("Z", printZonotope dops.showExact (dz.Z.reduceShortest (maxGens - dz.n)))])
  | _ => none

/-- Every op of `nnLayer.` this file serves, without the prefix. -/
def nnFormLayerOpNames : List String := [ "mergeBuckets", "groupSort", "generatorReduction" ]

/-- `neuralNetwork.normalForm`: the layers fused between the activations. -/
def normalFormOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "normalForm" req ["layers", "n"]
  let n ← natField req "n"
  let (⟨_, N⟩, names) ← aux_build dops n (← arrField req "layers").toList
  pure [("layers", Json.arr (aux_print dops N.normalForm names).toArray)]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
