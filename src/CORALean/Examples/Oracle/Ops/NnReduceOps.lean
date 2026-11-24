import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.Examples.Oracle.Ops.NnOps

/-!
# The reduced network: CORA's computeReducedNetwork with static buckets

A network is CORA.cpp's list of layers `{W, b, activation}`, every activation a ReLU but the last
(the chain is its own normal form). At each ReLU the output range of every neuron (CORA.cpp's
interval arithmetic from the box of the set) is compared with the bucket `0`: two or more neurons
within the tolerance of it are merged away, their ranges through the next matrix that layer's
error interval `dc +- dr`. A target rate searches the tolerance by CORA.cpp's bisection. The set
goes through each reduced layer (a box generator per row of `dr`) and its ReLU at the regression
line. `nearest` only; dynamic buckets and input compression are not served.

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

open CORALean CORALean.Float FloatOps
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A layer of the chain as rows: `W` (`m` rows of `n`), `b`, the error interval `dc`, `dr`. -/
private structure ChainLayer (𝕋 : Type) where
  n : ℕ
  W : Array (Array 𝕋)
  b : Array 𝕋
  d : Option (Array 𝕋 × Array 𝕋)
  relu : Bool

/-- The empty layer, the default of a lookup. -/
private def aux_noLayer : ChainLayer 𝕋 := ⟨0, #[], #[], none, false⟩

/-- `W x` of a matrix of rows and `n` columns, the sums of `Interval.mtimes` at a point. -/
private def aux_mv (W : Array (Array 𝕋)) (n : ℕ) (x : Array 𝕋) : Array 𝕋 :=
  let M : Mat 𝕋 W.size n := Matrix.of fun i j => (W.getD i.1 #[]).getD j.1 zero
  let v : Vec 𝕋 n := fun j => x.getD j.1 zero
  Array.ofFn (Interval.mtimes M (Interval.point v)).inf

/-- Entry by entry. -/
private def aux_zip (f : 𝕋 → 𝕋 → 𝕋) (a b : Array 𝕋) : Array 𝕋 := (a.zip b).map fun (x, y) => f x y

/-- CORA.cpp's interval arithmetic through layer `L` (`aux_affine_box`), then its ReLU. -/
private def aux_box (L : ChainLayer 𝕋) (lo hi : Array 𝕋) : Array 𝕋 × Array 𝕋 :=
  let mid := aux_zip (fun h l => half (addUp h l)) hi lo
  let rad := aux_zip (fun h l => half (subUp h l)) hi lo
  let mu := aux_zip addUp (aux_mv L.W L.n mid) L.b
  let r := aux_mv (L.W.map (·.map absolute)) L.n rad
  let (l, u) := (aux_zip subDown mu r, aux_zip addUp mu r)
  let (l, u) := match L.d with
    | none => (l, u)
    | some (dc, dr) =>
      (aux_zip addDown l (aux_zip subDown dc dr), aux_zip addUp u (aux_zip addUp dc dr))
  if L.relu then (l.map (maximum · zero), u.map (maximum · zero)) else (l, u)

/-- The zonotope of `c` and the generators `G` (each a row of the dimension). -/
private def aux_zonotope (c : Array 𝕋) (G : Array (Array 𝕋)) : Zonotope (Vec 𝕋 c.size) :=
  ⟨G.size, fun i => c.getD i.1 zero, fun l i => (G.getD l.1 #[]).getD i.1 zero,
    ⟨fun _ => zero, fun _ => zero⟩⟩

/-- The box of a set of rows: `c -+ sum |g|` (`Zonotope.interval`). -/
private def aux_setBox (c : Array 𝕋) (G : Array (Array 𝕋)) : Array 𝕋 × Array 𝕋 :=
  let I := (aux_zonotope c G).interval
  (Array.ofFn I.inf, Array.ofFn I.sup)

/-- The set through layer `L`: `W c + b (+ dc)`, `W g`, a box generator per row of `dr`, then the
ReLU at the regression line (`neuralNetwork.evaluate`). -/
private def aux_set (dops : DtypeOps 𝕋) (L : ChainLayer 𝕋) (c : Array 𝕋) (G : Array (Array 𝕋)) :
    Except String (Array 𝕋 × Array (Array 𝕋)) := do
  let m := L.W.size
  let c' := aux_zip addUp (aux_mv L.W L.n c) L.b
  let G' := G.map (aux_mv L.W L.n ·)
  let (c', G') := match L.d with
    | none => (c', G')
    | some (dc, dr) => (aux_zip addUp c' dc,
        G' ++ Array.ofFn fun i : Fin m => Array.ofFn fun j : Fin m =>
          if i = j then dr.getD i.1 zero else zero)
  if !L.relu then return (c', G')
  let req := Json.mkObj [("layers", Json.arr #[Json.mkObj [("kind", "relu")]]),
    ("poly_method", "regression"), ("regression_error", "extremum")]
  let ⟨k, Y⟩ ← networkOnZonotope dops "computeReducedNetwork" req c'.size (aux_zonotope c' G')
  pure (Array.ofFn (n := k) Y.c, Array.ofFn fun l => Array.ofFn (n := k) (Y.G l))

/-- CORA's withinTol: absolute or relative distance at most `tol` (the infinite case is not met:
the box of a finite set is finite). -/
private def aux_within (a b tol : 𝕋) : Bool :=
  let d := absolute (subUp a b)
  le d tol || le (divUp d (minimum (absolute a) (absolute b))) tol

/-- The neurons merged at the tolerance (the bucket `0` holding two or more), and whether any. -/
private def aux_merge (lo hi : Array 𝕋) (tol : 𝕋) : Array Bool × Bool :=
  let inBucket := (lo.zip hi).map fun (l, u) => le (subDown zero tol) l && le u (addUp zero tol)
  let count := (inBucket.filter id).size
  (inBucket.map (· && count > 1), count > 1)

/-- The rate of neurons that stay. -/
private def aux_rate (dops : DtypeOps 𝕋) (merged : Array Bool) : Except String 𝕋 := do
  let stay ← dops.readExact "count" (.dy ⟨(merged.filter (!·)).size, 0⟩)
  pure (divUp stay (← dops.readExact "count" (.dy ⟨merged.size, 0⟩)))

/-- CORA.cpp's bisection of the tolerance until the rate is met (or once, without a rate). -/
private def aux_search (dops : DtypeOps 𝕋) (lo hi : Array 𝕋) (want : Option 𝕋) :
    ℕ → ℤ → 𝕋 → 𝕋 → 𝕋 → Except String (Array Bool × Bool)
  | 0, _, _, _, _ => throw "computeReducedNetwork: the rate was not reached"
  | fuel + 1, searches, tol, tmin, tmax => do
    let searches := searches - 1
    let (merged, used) := aux_merge lo hi tol
    match want with
    | none => pure (merged, used)
    | some w =>
      let got ← aux_rate dops merged
      if (le w got && le got w) || (searches ≤ 0 && le got w) then return (merged, used)
      let two := addUp one one
      let (tol', tmin', tmax') :=
        if !(le w got) then (divUp (addUp tmin tol) two, tmin, tol)
        else (divUp (addUp tol tmax) two, tol, tmax)
      let ε ← dops.readExact "end" (.dy ⟨7737125245533627, -86⟩)
      let tol' := if aux_within tmin' tmax' ε then tmax' else tol'
      aux_search dops lo hi want fuel searches tol' tmin' tmax'

/-- The values of an optional array of scalars of the request, one for all or one per layer. -/
private def aux_perLayer (dops : DtypeOps 𝕋) (req : Json) (name : String) (m : ℕ) :
    Except String (Option (Array 𝕋)) := do
  match fieldOpt req name with
  | none => pure none
  | some _ =>
    let v ← (← arrField req name).mapM fun j => do
      dops.readExact name (← scalarField (Json.mkObj [("v", j)]) "v")
    if v.size = 1 then pure (some (Array.replicate m (v.getD 0 zero)))
    else if v.size = m then pure (some v)
    else throw s!"computeReducedNetwork: `{name}` takes one value or one per layer ({m})"

/-- The reduction of the chain: every layer followed by another merged, then the last layer. -/
private def aux_reduce (dops : DtypeOps 𝕋) (minSearches : ℕ) (tol : Array 𝕋)
    (rate : Option (Array 𝕋)) (chain : Array (ChainLayer 𝕋)) (c : Array 𝕋)
    (G : Array (Array 𝕋)) :
    Except String (Array (ChainLayer 𝕋) × Array (Option (Array Bool)) × Array 𝕋 ×
      Array (Array 𝕋)) := do
  let m := chain.size
  let mut chain := chain
  let mut merged : Array (Option (Array Bool)) := Array.replicate m none
  let (c₀, G₀) := (c, G)
  let mut c := c₀
  let mut G := G₀
  let mut bounds := aux_setBox c G
  for j in [0:m - 1] do
    let L := chain.getD j aux_noLayer
    let (lo, hi) := aux_box L bounds.1 bounds.2
    -- the tolerance, searched by bisection if a rate is asked for
    let tmax := subUp (hi.foldl maximum (hi.getD 0 zero)) (lo.foldl minimum (lo.getD 0 zero))
    let (mk', used) ← aux_search dops lo hi (rate.map (·.getD j zero)) 2000 minSearches
      (tol.getD j zero) zero tmax
    merged := merged.set! j (some mk')
    let keep := (List.range mk'.size).filter fun i => !mk'.getD i false
    let mask := mk'.map fun b => if b then one else zero
    -- the next layer reads the neurons that stay; the ones merged go in as an interval
    let N := chain.getD (j + 1) aux_noLayer
    let d := if used then
        let mid := aux_zip mulUp (aux_zip (fun l u => half (addUp l u)) lo hi) mask
        let rad := aux_zip mulUp (aux_zip (fun l u => half (subUp u l)) lo hi) mask
        let dc := aux_mv N.W N.n mid
        let dr := aux_mv (N.W.map (·.map absolute)) N.n rad
        match N.d with
        | none => some (dc, dr)
        | some (dc₀, dr₀) => some (aux_zip addUp dc dc₀, aux_zip addUp dr dr₀)
      else N.d
    let rows (a : Array 𝕋) : Array 𝕋 := (keep.map fun i => a.getD i zero).toArray
    let rowsW : Array (Array 𝕋) := (keep.map fun i => L.W.getD i #[]).toArray
    let dj : Option (Array 𝕋 × Array 𝕋) := match L.d with
      | none => none
      | some (dc, dr) => some (rows dc, rows dr)
    chain := chain.set! (j + 1) ⟨keep.length, N.W.map rows, N.b, d, N.relu⟩
    chain := chain.set! j ⟨L.n, rowsW, rows L.b, dj, L.relu⟩
    -- the set through the reduced layer, and its box for the next one
    let (c', G') ← aux_set dops (chain.getD j aux_noLayer) c G
    c := c'
    G := G'
    bounds := aux_setBox c G
  let (c', G') ← aux_set dops (chain.getD (m - 1) aux_noLayer) c G
  pure (chain, merged, c', G')

/-- A vector of the dtype as the wire's column. -/
private def aux_printArr (dops : DtypeOps 𝕋) (a : Array 𝕋) : Json :=
  printVec dops.showExact (n := a.size) fun i => a[i]

/-- A matrix of rows as the wire's matrix. -/
private def aux_printRows (dops : DtypeOps 𝕋) (W : Array (Array 𝕋)) (n : ℕ) : Json :=
  printMat dops.showExact (r := W.size) (c := n)
    (Matrix.of fun i j => (W.getD i.1 #[]).getD j.1 zero)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `neuralNetwork.computeReducedNetwork` with static buckets. -/
def computeReducedNetworkOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "computeReducedNetwork"
  checkFields op req ["layers", "Z", "bucketTol", "reductionRate", "minSearches"]
  if dops.guaranteed then
    throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the merging decides on \
      rounded values; use dtype `nearest`"
  else pure ()
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let layers := (← arrField req "layers").toList
  -- the chain, every activation a ReLU but the last
  let (chain, _) ← layers.foldlM (fun (acc : Array (ChainLayer 𝕋) × ℕ) L => do
    checkFields op L ["W", "b", "activation"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact acc.2 (← field L "W")
    let b ← parseVecFixed dops.readExact m (← field L "b")
    let relu ← match ← strField L "activation" with
      | "relu" => pure true
      | "identity" => pure false
      | a => throw s!"{op}: the activations are relu (the last may be identity), not `{a}`"
    let rows := Array.ofFn fun i : Fin m => Array.ofFn fun j : Fin acc.2 => W i j
    pure (acc.1.push ⟨acc.2, rows, Array.ofFn b, none, relu⟩, m)) (#[], dz.n)
  let m := chain.size
  if m = 0 then throw s!"{op}: the network has no layer"
  if (chain.toList.dropLast).any (!·.relu) then
    throw s!"{op}: every activation but the last is a relu"
  -- the tolerances (CORA's bucket width 0.01 by default) and the rates
  let tol ← match ← aux_perLayer dops req "bucketTol" m with
    | some t => pure t
    | none => pure (Array.replicate m (← dops.readExact "bucketTol" (.dy ⟨5764607523034235, -59⟩)))
  let rate ← aux_perLayer dops req "reductionRate" m
  let minSearches := (natField req "minSearches").toOption.getD 10
  let c := Array.ofFn dz.Z.c
  let G := Array.ofFn fun l => Array.ofFn (dz.Z.G l)
  let counts (ch : Array (ChainLayer 𝕋)) : List ℕ :=
    (ch.getD 0 aux_noLayer).n :: ch.toList.map (·.W.size)
  -- a rate of 1 asks for no reduction: the set goes through the network as it is
  let plain := match rate with
    | some r => r.all (le one ·) && r.any (le · one)
    | none => false
  let (out, merged, c', G') ← if plain then do
      let (c', G') ← chain.foldlM (fun (s : Array 𝕋 × Array (Array 𝕋)) L => aux_set dops L s.1 s.2)
        (c, G)
      pure (chain, Array.replicate m none, c', G')
    else aux_reduce dops minSearches tol rate chain c G
  -- the rate of neurons that stay: the target, or the ratio of the counts
  let rates ← match rate with
    | some r => pure r
    | none => ((counts out).zip (counts chain)).toArray.mapM fun (a, b) => do
        let (a, b) := (← dops.readExact "count" (.dy ⟨a, 0⟩), ← dops.readExact "count" (.dy ⟨b, 0⟩))
        pure (divUp a b)
  pure [("layers", Json.arr (out.map fun L => Json.mkObj [("W", aux_printRows dops L.W L.n),
      ("b", aux_printArr dops L.b), ("activation", if L.relu then "relu" else "identity")])),
    ("d", Json.arr (out.map fun L => match L.d with
      | none => Json.null
      | some (dc, dr) => Json.mkObj [("c", aux_printArr dops dc), ("r", aux_printArr dops dr)])),
    ("merged", Json.arr (merged.map fun o => match o with
      | none => Json.null
      | some v => Lean.toJson (v.toList.map fun b => if b then 1 else 0))),
    ("reductionRate", aux_printArr dops rates),
    ("Z", printZonotope dops.showExact (aux_zonotope c' G'))]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
