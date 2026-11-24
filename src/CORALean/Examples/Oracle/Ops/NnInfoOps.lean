import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The structure of a network: CORA's neuron and parameter counts, refinable layers, patterns

A network is CORA.cpp's list of layers `{W, b, activation}`; only the shapes and the activations
are read, so every reply is integers. `getNumNeurons` is the input width of every layer and the
output width of the last; `getNumParams` the entries of every `W` and `b`; `getRefinableLayers` the
0-based layers whose activation is not the identity. `getOrderPattern` is the order of every
neuron of those layers, from the `orders` given per layer (CORA.cpp's `aux_expand`).
`prepareForZonoBatchEval` is CORA's `numGen` after the last layer and the generators each
activation layer adds for its approximation errors.

## Inputs
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

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A layer's shape `(out, in)` and whether its activation is not the identity. -/
private def aux_shape (op : String) (layer : Json) : Except String (ℕ × ℕ × Bool) := do
  checkFields op layer ["W", "b", "activation"]
  let W ← field layer "W"
  let m ← natField W "rows"
  let b ← field layer "b"
  if (← natField b "rows") ≠ m then throw s!"{op}: a layer's `b` has one entry per row of `W`"
  let act ← strField layer "activation"
  pure (m, ← natField W "cols", act != "identity")

/-- The layers' shapes, each reading the one before. -/
private def aux_shapes (op : String) (req : Json) : Except String (List (ℕ × ℕ × Bool)) := do
  let L ← (← arrField req "layers").toList.mapM (aux_shape op)
  if L.isEmpty then throw s!"{op}: the network has no layer"
  let ok := (L.zip L.tail).all fun ((m, _, _), (_, n, _)) => m = n
  if !ok then throw s!"{op}: a layer reads as many inputs as the one before has outputs"
  pure L

/-- A count option: a natural number, or `inf` (also when absent). -/
private def aux_count (req : Json) (name : String) : Except String (Option ℕ) :=
  match fieldOpt req name with
  | none | some (.str "inf") => pure none
  | some _ => do pure (some (← natField req name))

/-- The orders of a layer of `n` neurons from the given ones (CORA.cpp's `aux_expand`). -/
private def aux_expand (given : List ℕ) (n : ℕ) : List ℕ :=
  if given.isEmpty then List.replicate n 1
  else if given.length = n then given
  else List.replicate n (given.foldl max 0)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `neuralNetwork.` from this file, run; `none` for a name it does not serve. -/
def handleNnInfoOp (op : String) (req : Json) : Option Resp :=
  match op with
  | "getNumNeurons" => some (do
    checkFields op req ["layers"]
    let L ← aux_shapes op req
    pure [("numNeurons", Lean.toJson (L.map (·.2.1) ++ [(L.getLast?.map (·.1)).getD 0]))])
  -- the counts
  | "getNumParams" => some (do
    checkFields op req ["layers"]
    let L ← aux_shapes op req
    pure [("numParams", Lean.toJson ((L.map fun (m, n, _) => m * n + m).sum))])
  | "getRefinableLayers" => some (do
    checkFields op req ["layers"]
    let L ← aux_shapes op req
    let refinable := (List.range L.length).filter fun k => (L.getD k (0, 0, false)).2.2
    pure [("layers", Lean.toJson refinable)])
  -- the orders of the refinable layers' neurons
  | "getOrderPattern" => some (do
    checkFields op req ["layers", "orders"]
    let L ← aux_shapes op req
    let orders ← match fieldOpt req "orders" with
      | none => pure []
      | some _ => (← arrField req "orders").toList.mapM fun o =>
          match Lean.fromJson? (α := List ℕ) o with
          | .ok v => pure v
          | .error _ => throw s!"{op}: `orders` is a list of lists of naturals, one per layer"
    let pattern := ((List.range L.length).filter fun k => (L.getD k (0, 0, false)).2.2).map
      fun k => aux_expand (orders.getD k []) (L.getD k (0, 0, false)).1
    pure [("pattern", Lean.toJson pattern)])
  | "prepareForZonoBatchEval" => some (do
    checkFields op req ["layers", "numInitGens", "numApproxErr"]
    let L ← aux_shapes op req
    let n₀ := (L.headD (0, 0, false)).2.1
    -- the input's generators, then the error generators of each activation layer in turn
    let q₀ := (← aux_count req "numInitGens").getD n₀
    let e ← aux_count req "numApproxErr"
    let (q, added) := L.foldl (fun (q, acc) (m, _, act) =>
      let d := if act then (e.map (min m)).getD m else 0
      (q + d, acc ++ [if act then Json.arr #[Lean.toJson q, Lean.toJson d] else Json.null]))
      (q₀, [])
    pure [("numGen", Lean.toJson q), ("approxErrGens", Json.arr added.toArray)])
  | _ => none

/-- Every op of `neuralNetwork.` this file serves, without the prefix. -/
def nnInfoOpNames : List String :=
  [ "getNumNeurons", "getNumParams", "getRefinableLayers", "getOrderPattern",
    "prepareForZonoBatchEval" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
