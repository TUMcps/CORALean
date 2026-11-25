import CORALean.Global.Float.LogDownPos
import CORALean.Global.Float.SqrtDownCora
import CORALean.Global.Float.TrigRange
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The weights and the orders of a network: CORA's castWeights, generateRandom, initWeights, refine

A network is CORA.cpp's list of layers `{W, b, activation}`. `castWeights` rounds every weight and
bias to nearest in the request's dtype (CORA casts them to `single`). `generateRandom` and
`initWeights` take CORA.cpp's uniform draws in `(0, 1]` as inputs, in the order its `Rng` makes
them, and do the arithmetic on them: CORA.cpp's `randi` for a size not given, `u (hi - lo) + lo`
for a uniform weight, Box-Muller for `shi`'s normal ones, or (`normals`) the standard normals
themselves, scaled afterwards as CORA's `normrnd` does. `resetApproxOrder` is the order 1 of every
neuron of the refinable layers. `refine` raises the orders by a heuristic given per neuron (CORA's
types `all`, `layer` and `neuron`), at `nearest` only: its replies are decisions on rounded values.

## Inputs
* `dops` – dtype operations
* `op` – op name, without the prefix
* `req` – request

## Output
* the op's reply
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   25-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float FloatOps
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The refusal of an op whose reply is a decision on rounded values, at a guaranteed dtype. -/
private def aux_requireNearest (dops : DtypeOps 𝕋) (op : String) : Except String Unit :=
  if dops.guaranteed then
    throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the reply decides on \
      rounded values, which a box cannot; use dtype `nearest`"
  else pure ()

/-- A layer's shape `(out, in)` and its activation's name. -/
private def aux_shape (op : String) (layer : Json) : Except String (ℕ × ℕ × String) := do
  checkFields op layer ["W", "b", "activation"]
  let W ← field layer "W"
  let m ← natField W "rows"
  if (← natField (← field layer "b") "rows") ≠ m then
    throw s!"{op}: a layer's `b` has one entry per row of `W`"
  pure (m, ← natField W "cols", ← strField layer "activation")

/-- The layers' shapes, each reading the one before. -/
private def aux_shapes (op : String) (req : Json) : Except String (List (ℕ × ℕ × String)) := do
  let L ← (← arrField req "layers").toList.mapM (aux_shape op)
  if L.isEmpty then throw s!"{op}: the network has no layer"
  if !(L.zip L.tail).all fun ((m, _, _), (_, n, _)) => m = n then
    throw s!"{op}: a layer reads as many inputs as the one before has outputs"
  pure L

/-- The orders of a layer of `n` neurons from the given ones (CORA.cpp's `aux_expand`). -/
private def aux_expand (given : List ℕ) (n : ℕ) : List ℕ :=
  if given.isEmpty then List.replicate n 1
  else if given.length = n then given
  else List.replicate n (given.foldl max 0)

/-- The `orders` of the request, a list of naturals per layer (none: every order 1). -/
private def aux_orders (op : String) (req : Json) : Except String (List (List ℕ)) :=
  match fieldOpt req "orders" with
  | none => pure []
  | some _ => do
    (← arrField req "orders").toList.mapM fun o =>
      match Lean.fromJson? (α := List ℕ) o with
      | .ok v => pure v
      | .error _ => throw s!"{op}: `orders` is a list of lists of naturals, one per layer"

/-- The natural number `k` in the dtype (exact for the small counts it is used at). -/
private def aux_nat (dops : DtypeOps 𝕋) (k : ℕ) : Except String 𝕋 :=
  dops.readExact "count" (.dy ⟨k, 0⟩)

/-- The entries of a wire matrix (or column) read in the dtype, row-major, with its shape. -/
private def aux_values (dops : DtypeOps 𝕋) (j : Json) : Except String (ℕ × ℕ × Array 𝕋) := do
  let dm ← parseMatScalarDyn j
  pure (dm.r, dm.c, ← dm.data.mapM (dops.readExact "draw"))

/-- Row-major values as the wire's box `{inf, sup}` of an `r × c` matrix. -/
private def aux_printBox (dops : DtypeOps 𝕋) (r c : ℕ) (lo hi : Array 𝕋) : Json :=
  let M (a : Array 𝕋) : Mat 𝕋 r c := Matrix.of fun i j => a.getD (i.1 * c + j.1) zero
  printIntervalMat dops.showExact ⟨M lo, M hi⟩

/-- The box of the product of two boxes `[a, b] [c, d]`. -/
private def aux_mulBox (x y : 𝕋 × 𝕋) : 𝕋 × 𝕋 :=
  let (a, b) := x
  let (c, d) := y
  (minimum (minimum (mulDown a c) (mulDown a d)) (minimum (mulDown b c) (mulDown b d)),
    maximum (maximum (mulUp a c) (mulUp a d)) (maximum (mulUp b c) (mulUp b d)))

/-- The uniform draw `u (hi - lo) + lo` of CORA.cpp's `Rng::uniform`, `u ≥ 0`, as a box, where
`span = hi - lo` and `lo` are boxes. -/
private def aux_uniform (span lo : 𝕋 × 𝕋) (u : 𝕋) : 𝕋 × 𝕋 :=
  let s := aux_mulBox (u, u) span
  (addDown s.1 lo.1, addUp s.2 lo.2)

/-- CORA.cpp's `aux_randi`: `min(hi, lo + floor(u (hi - lo + 1)))`, refused if the box of the
product straddles an integer. -/
private def aux_randi (dops : DtypeOps 𝕋) (op : String) (u : 𝕋) (lo hi : ℕ) :
    Except String ℕ := do
  let N ← aux_nat dops (hi - lo + 1)
  let a := (ToRat.toRat (mulDown u N)).floor
  let b := (ToRat.toRat (mulUp u N)).floor
  if a ≠ b ∨ a < 0 then throw s!"{op}: a size draw is not decided at this dtype"
  pure (min hi (lo + a.toNat))

/-- `log a` from above at `0 < a < 1` too: the format's own where it has one, else
`-(log(1 / a))` from below, `logDown` of the quotient rounded down (`logUp` bisects over `[0, a]`
and stops at `0` below `1`). -/
private def aux_logUpPos (n k : ℕ) (a : 𝕋) : 𝕋 :=
  match elemOverride (𝕋 := 𝕋) with
  | some e => e.log a
  | none => if le one a then logUp n k a else neg (logDown n k (divDown one a))

/-- The Box-Muller normals of CORA.cpp's `Rng::normal` at `scale` from its units `u` (pairs, and
the two units of an odd last one), as boxes. -/
private def aux_normals (scale : 𝕋 × 𝕋) (twoPi : 𝕋) (count : ℕ) (u : Array 𝕋) :
    Array (𝕋 × 𝕋) :=
  let p := 60
  let two := addUp one one
  -- the radius `scale sqrt(-2 log u₁)` and the angle `2π u₂`
  let radius (a : 𝕋) : 𝕋 × 𝕋 :=
    let L := (logDownPos p p a, aux_logUpPos p p a)
    let m := aux_mulBox (neg two, neg two) L
    aux_mulBox scale (sqrtDownCora p m.1, sqrtUp p m.2)
  let angle (a : 𝕋) : 𝕋 × 𝕋 := (mulDown twoPi a, mulUp twoPi a)
  let cosB (x : 𝕋 × 𝕋) : 𝕋 × 𝕋 := let I := cosRange p x.1 x.2; (I.inf, I.sup)
  let sinB (x : 𝕋 × 𝕋) : 𝕋 × 𝕋 := let I := sinRange p x.1 x.2; (I.inf, I.sup)
  Array.ofFn fun k : Fin count =>
    let i := k.1 / 2 * 2
    let r := radius (u.getD i zero)
    let θ := angle (u.getD (i + 1) zero)
    if k.1 % 2 = 0 then aux_mulBox r (cosB θ) else aux_mulBox r (sinB θ)

/-- The heuristic of each layer: the values given (absent ones 0), cut to the layer's neurons. -/
private def aux_heuristic (dops : DtypeOps 𝕋) (op : String) (req : Json) (k n : ℕ) :
    Except String (List 𝕋) := do
  let given ← match fieldOpt req "heuristic" with
    | none => pure #[]
    | some _ => arrField req "heuristic"
  let vals ← match given[k]? with
    | none | some .null => pure #[]
    | some j => do
      match j with
      | .arr a => a.mapM fun v => do
          dops.readExact "heuristic" (← scalarField (Json.mkObj [("h", v)]) "h")
      | _ => throw s!"{op}: `heuristic` is a list of lists of scalars, one per layer"
  pure ((List.range n).map fun j => vals.getD j zero)

/-- `a > b` and `a ≠ b` at the dtype's comparison. -/
private def aux_gt (a b : 𝕋) : Bool := !(le a b)

/-- One step of CORA.cpp's `refine`: the orders of every layer after it. -/
private def aux_refine (dops : DtypeOps 𝕋) (op : String) (req : Json) :
    Except String (List (List ℕ)) := do
  -- the network, the orders and the options (CORA's defaults: 5, 0.1, the layer type)
  let L ← aux_shapes op req
  let orders ← aux_orders op req
  let maxOrder := (natField req "maxOrder").toOption.getD 5
  if maxOrder = 0 then throw s!"{op}: `maxOrder` is at least 1"
  let gamma ← match fieldOpt req "gamma" with
    | none => dops.readExact "gamma" (.dy ⟨7205759403792794, -56⟩)
    | some _ => do dops.readExact "gamma" (← scalarField req "gamma")
  let kind := (strField req "heuristicKind").toOption.getD "approx_error"
  let type0 := (strField req "type").toOption.getD "layer"
  if kind ∉ ["approx_error", "layer_bias", "all"] then
    throw s!"{op}: `heuristicKind` is approx_error, layer_bias or all, not `{kind}`"
  if type0 ∉ ["all", "layer", "neuron"] then
    throw s!"{op}: `type` is all, layer or neuron, not `{type0}`"
  -- the orders of every neuron, and the heuristic of the refinable layers
  let out := (List.range L.length).map fun k =>
    aux_expand (orders.getD k []) (L.getD k (0, 0, "")).1
  let refinable := (List.range L.length).filter fun k => (L.getD k (0, 0, "")).2.2 != "identity"
  let heu ← (List.range L.length).mapM fun k => do
    match refinable.findIdx? (· == k) with
    | none => pure []
    | some i => do
      let v ← aux_heuristic dops op req k (L.getD k (0, 0, "")).1
      if kind = "layer_bias" then
        let d ← aux_nat dops (i + 1)
        pure (v.map fun x => divUp x d)
      else pure v
  let type := if kind = "all" then "all" else type0
  let bump (o : List ℕ) (pick : ℕ → Bool) : List ℕ :=
    (List.range o.length).map fun j => if pick j then o.getD j 0 + 1 else o.getD j 0
  match type with
  -- every refinable neuron by one, at most maxOrder
  | "all" =>
    pure ((List.range out.length).map fun k =>
      if refinable.contains k then (out.getD k []).map fun o => min (o + 1) maxOrder
      else out.getD k [])
  | "layer" =>
    -- the largest 2-norm among the layers below maxOrder, the earlier layer on ties
    let best := refinable.foldl (fun (acc : Option (𝕋 × ℕ)) k =>
      let o := out.getD k []
      let sq := (heu.getD k []).foldl (fun s v => addUp s (mulUp v v)) zero
      let norm := sqrtUp 60 sq
      if o.foldl max 0 < maxOrder ∧ aux_gt norm zero then
        match acc with
        | none => some (norm, k)
        | some (n₀, k₀) => if aux_gt norm n₀ then some (norm, k) else some (n₀, k₀)
      else acc) none
    pure ((List.range out.length).map fun k =>
      match best with
      | some (_, k₀) => if k = k₀ then (out.getD k []).map (· + 1) else out.getD k []
      | none => out.getD k [])
  | _ =>
    -- the neurons above gamma times the largest heuristic, in the layer of the largest
    let cands := refinable.flatMap fun k =>
      ((List.range (out.getD k []).length).filter fun j =>
        (out.getD k []).getD j 0 < maxOrder ∧ aux_gt ((heu.getD k []).getD j zero) zero).map
        fun j => ((heu.getD k []).getD j zero, k, j)
    match cands.foldl (fun (acc : Option (𝕋 × ℕ × ℕ)) c =>
        match acc with
        | none => some c
        | some a => if aux_gt c.1 a.1 then some c else some a) none with
    | none => pure out
    | some (largest, k₀, _) =>
      let bound := mulUp gamma largest
      pure ((List.range out.length).map fun k =>
        bump (out.getD k []) fun j =>
          k = k₀ ∧ cands.any fun (h, k', j') => k' = k ∧ j' = j ∧ aux_gt h bound)

/-- CORA.cpp's `NeuralNetwork::random` on the draws: the sizes, then each layer's `W` and `b`. -/
private def aux_generateRandom (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  checkFields op req ["inputs", "outputs", "layers", "hidden", "sizeDraws", "draws"]
  let sizeDraws ← match fieldOpt req "sizeDraws" with
    | none => pure #[]
    | some j => do pure (← aux_values dops j).2.2
  -- the sizes not given, drawn in CORA's order
  let given (name : String) : ℕ := (natField req name).toOption.getD 0
  let step (name : String) (lo hi : ℕ) (s : List ℕ × ℕ) : Except String (List ℕ × ℕ) := do
    if given name ≠ 0 then pure (s.1 ++ [given name], s.2) else
      let u ← match sizeDraws[s.2]? with
        | some u => pure u
        | none => throw s!"{op}: `sizeDraws` has no draw for `{name}`"
      pure (s.1 ++ [← aux_randi dops op u lo hi], s.2 + 1)
  let s ← step "inputs" 1 5 ([], 0) >>= step "outputs" 1 5 >>= step "layers" 1 5 >>=
    step "hidden" 2 20
  let (sizes, used) := s
  if used ≠ sizeDraws.size then throw s!"{op}: `sizeDraws` has {sizeDraws.size} draws, not {used}"
  let (inputs, outputs, depth, hidden) :=
    (sizes.getD 0 0, sizes.getD 1 0, sizes.getD 2 0, sizes.getD 3 0)
  let neurons := (List.range (depth + 1)).map fun i =>
    if i = 0 then inputs else if i = depth then outputs else hidden
  let draws ← arrField req "draws"
  if draws.size ≠ depth then throw s!"{op}: `draws` has one entry per layer, {depth}"
  -- each layer: `u 2 + (-1)`, the weights in [-1, 1)
  let two := addUp one one
  let span : 𝕋 × 𝕋 := (two, two)
  let lo : 𝕋 × 𝕋 := (neg one, neg one)
  let layers ← (List.range depth).mapM fun i => do
    let (m, n) := (neurons.getD (i + 1) 0, neurons.getD i 0)
    let d := draws[i]!
    let (rW, cW, uW) ← aux_values dops (← field d "W")
    let (rb, _, ub) ← aux_values dops (← field d "b")
    if rW ≠ m ∨ cW ≠ n ∨ rb ≠ m then throw s!"{op}: the draws of layer {i} are not {m} x {n}"
    let W := uW.map (aux_uniform span lo)
    let b := ub.map (aux_uniform span lo)
    pure (Json.mkObj [("W", aux_printBox dops m n (W.map (·.1)) (W.map (·.2))),
      ("b", aux_printBox dops m 1 (b.map (·.1)) (b.map (·.2)))])
  pure [("inputs", Lean.toJson inputs), ("outputs", Lean.toJson outputs),
    ("layers", Lean.toJson depth), ("hidden", Lean.toJson hidden),
    ("network", Json.arr layers.toArray)]

/-- CORA.cpp's `init_weights` on the draws: the weights of the layers `which` again, biases 0. -/
private def aux_initWeights (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  checkFields op req ["layers", "method", "which", "draws", "normals"]
  let L ← aux_shapes op req
  let method := (strField req "method").toOption.getD "glorot"
  if method ∉ ["glorot", "shi"] then throw s!"{op}: `method` is glorot or shi, not `{method}`"
  let which ← match fieldOpt req "which" with
    | none => pure (List.range L.length)
    | some _ => do pure (← natArrField req "which").toList
  -- shi's standard normals given (CORA's `randn .* sigma`), or the units of Box-Muller
  let normals := (fieldOpt req "normals").isSome
  if normals ∧ (method ≠ "shi" ∨ (fieldOpt req "draws").isSome) then
    throw s!"{op}: `normals` replaces `draws`, for shi only"
  let draws ← arrField req (if normals then "normals" else "draws")
  let redrawn := (List.range L.length).filter which.contains
  if draws.size ≠ redrawn.length then
    throw s!"{op}: `draws` has one entry per layer drawn again, {redrawn.length}"
  -- CORA.cpp's constant 6.283185307179586, the double nearest 2π (Box-Muller's angle)
  let twoPi ← dops.readExact "twoPi" (.dy ⟨7074237752028440, -50⟩)
  let p := 60
  let layers ← (List.range L.length).mapM fun k => do
    let layer := (← arrField req "layers")[k]!
    let (m, n, act) := L.getD k (0, 0, "")
    match redrawn.findIdx? (· == k) with
    | none => pure layer
    | some i => do
      let (_, _, u) ← aux_values dops draws[i]!
      let N ← aux_nat dops n
      let W ← if method = "glorot" then do
          -- `a = 1 / sqrt(n)`, the weights `u (a - (-a)) + (-a)`
          if u.size ≠ m * n then throw s!"{op}: layer {k} takes {m * n} draws"
          let a : 𝕋 × 𝕋 := (divDown one (sqrtUp p N), divUp one (sqrtDownCora p N))
          let span := (addDown a.1 a.1, addUp a.2 a.2)
          pure (u.map (aux_uniform span (neg a.2, neg a.1)))
        else if normals then do
          -- `sqrt(2 pi) / n` times each standard normal given
          if u.size ≠ m * n then throw s!"{op}: layer {k} takes {m * n} normals"
          let r := (sqrtDownCora p twoPi, sqrtUp p twoPi)
          let scale := (divDown r.1 N, divUp r.2 N)
          pure (u.map fun z => aux_mulBox (z, z) scale)
        else do
          -- `sqrt(2 pi) / n`, the normals of Box-Muller at that scale
          if u.size ≠ m * n + (m * n) % 2 then
            throw s!"{op}: layer {k} takes {m * n + (m * n) % 2} draws"
          let r := (sqrtDownCora p twoPi, sqrtUp p twoPi)
          let scale := (divDown r.1 N, divUp r.2 N)
          pure (aux_normals scale twoPi (m * n) u)
      pure (Json.mkObj [("W", aux_printBox dops m n (W.map (·.1)) (W.map (·.2))),
        ("b", printVec dops.showExact (fun _ : Fin m => (zero : 𝕋))),
        ("activation", Json.str act)])
  pure [("layers", Json.arr layers.toArray)]

/-- Every entry of a wire matrix rounded to nearest in the dtype (CORA's cast to `single`). -/
private def aux_cast (dops : DtypeOps 𝕋) (j : Json) : Except String Json := do
  let dm ← parseMatScalarDyn j
  let vals ← dm.data.mapIdxM fun i d => match dops.roundToScalar "nearest" d with
    | .ok t => pure t.1
    | .error e => throw s!"castWeights: data[{i}]: {e}"
  pure (printMat dops.showExact (Matrix.of fun (i : Fin dm.r) (l : Fin dm.c) =>
    vals.getD (i.1 * dm.c + l.1) zero))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `neuralNetwork.` from this file, run; `none` for a name it does not serve. -/
@[noinline, nospecialize]
def handleNnWeightOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "castWeights" => some (do
    checkFields op req ["layers"]
    let layers ← (← arrField req "layers").toList.mapM fun L => do
      checkFields op L ["W", "b", "activation"]
      pure (Json.mkObj [("W", ← aux_cast dops (← field L "W")),
        ("b", ← aux_cast dops (← field L "b")), ("activation", ← field L "activation")])
    pure [("layers", Json.arr layers.toArray)])
  -- the orders: every one 1, or one step of the refinement
  | "resetApproxOrder" => some (do
    checkFields op req ["layers"]
    let L ← aux_shapes op req
    let pattern := (L.filter fun (_, _, a) => a != "identity").map fun (m, _, _) =>
      List.replicate m 1
    pure [("pattern", Lean.toJson pattern)])
  | "refine" => some (do
    checkFields op req ["layers", "orders", "heuristic", "type", "heuristicKind", "maxOrder",
      "gamma"]
    aux_requireNearest dops op
    pure [("orders", Lean.toJson (← aux_refine dops op req))])
  -- the weights on CORA.cpp's draws
  | "generateRandom" => some (aux_generateRandom dops op req)
  | "initWeights" => some (aux_initWeights dops op req)
  | _ => none

/-- Every op of `neuralNetwork.` this file serves, without the prefix. -/
def nnWeightOpNames : List String :=
  [ "castWeights", "resetApproxOrder", "refine", "generateRandom", "initWeights" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
