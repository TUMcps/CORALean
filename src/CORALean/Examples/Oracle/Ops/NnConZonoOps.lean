import CORALean.Global.Float.Sqrt
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# A network on a constrained zonotope: CORA's evaluateConZonotope with the box bounds

A network is CORA.cpp's list of layers `{W, b, activation}` (`relu` or `identity`) on a zonotope
without constraints, as a star set `c + G x`, `C x <= d`, `l <= x <= u`. A ReLU is taken neuron by
neuron, its bounds from the box of the factors (`bound_approx`): a neuron never positive is
zeroed, an unstable one a new factor `y` in `[0, up]` with the triangle's three rows. The star set
goes back as CORA.cpp's `conversionStarSetConZono`: rows scaled by their length, a row `+-1` of one
factor its bound, every other row an equality with a slack factor. Each step is CORA.cpp's loop.
`nearest` only; constraints (null space, linear programs) and LP bounds are not served.

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

/-- The star set `c + G x` (`G` as `n` rows of `k`), `C x <= d` (rows of `k`), `l <= x <= u`. -/
private structure Star (𝕋 : Type) where
  k : ℕ
  c : Array 𝕋
  G : Array (Array 𝕋)
  C : Array (Array 𝕋)
  d : Array 𝕋
  l : Array 𝕋
  u : Array 𝕋

/-- `0.5`, exact. -/
private def aux_half : 𝕋 := half one

/-- The left fold of the sum, from `0`, CORA.cpp's `acc +=`. -/
private def aux_sum (xs : List 𝕋) : 𝕋 := xs.foldl addUp zero

/-- The star set of a zonotope of `m` generators (rows of `Gt` are the generators). -/
private def aux_star (c : Array 𝕋) (gens : Array (Array 𝕋)) : Star 𝕋 :=
  let m := gens.size
  let unit (i : ℕ) (s : 𝕋) : Array 𝕋 := Array.ofFn fun q : Fin m => if q.1 = i then s else zero
  ⟨m, c, Array.ofFn fun a : Fin c.size => gens.map (·.getD a.1 zero),
    Array.ofFn (fun i : Fin m => unit i.1 one) ++ Array.ofFn (fun i : Fin m => unit i.1 (neg one)),
    Array.replicate (2 * m) one, Array.replicate m (neg one), Array.replicate m one⟩

/-- A linear layer: `c = W c + b`, `G = W G`, CORA.cpp's loops. -/
private def aux_affine (W : Array (Array 𝕋)) (b : Array 𝕋) (S : Star 𝕋) : Star 𝕋 :=
  let n := S.c.size
  let c := Array.ofFn fun i : Fin b.size =>
    let row := W.getD i.1 #[]
    addUp (aux_sum ((List.range n).map fun j => mulUp (row.getD j zero) (S.c.getD j zero)))
      (b.getD i.1 zero)
  let G := Array.ofFn fun i : Fin b.size => Array.ofFn fun q : Fin S.k =>
    aux_sum ((List.range n).map fun j =>
      mulUp ((W.getD i.1 #[]).getD j zero) ((S.G.getD j #[]).getD q.1 zero))
  { S with c := c, G := G }

/-- One ReLU neuron `j` at the box bounds of the factors (CORA's evaluateConZonotopeNeuron). -/
private def aux_relu (S : Star 𝕋) (j : ℕ) : Star 𝕋 :=
  let k := S.k
  let g := S.G.getD j #[]
  let gi (i : ℕ) : 𝕋 := g.getD i zero
  -- the bounds of the neuron by the box of the factors
  let (mid, rad) := (List.range k).foldl (fun (mid, rad) i =>
    let h := mulUp aux_half (gi i)
    (addUp mid (mulUp h (addUp (S.u.getD i zero) (S.l.getD i zero))),
      addUp rad (absolute (mulUp h (subUp (S.u.getD i zero) (S.l.getD i zero))))))
    (S.c.getD j zero, zero)
  let lo := subDown mid rad
  let up := addUp mid rad
  if !ltStrict lo zero then S else
  let cj := S.c.getD j zero
  -- the neuron zeroed in the center and the generators
  let c := S.c.set! j zero
  let G := S.G.set! j (Array.replicate k zero)
  if le up zero then { S with c := c, G := G } else
  -- a new factor y in [0, up]: y >= 0, y >= g x + c, y <= up / (up - lo) (g x + c - lo)
  let s := divUp up (subUp up lo)
  let ms := divUp (neg up) (subUp up lo)
  let C := S.C.map (·.push zero) ++
    #[(Array.replicate k zero).push (neg one), (Array.ofFn fun i : Fin k => gi i.1).push (neg one),
      (Array.ofFn fun i : Fin k => mulUp ms (gi i.1)).push one]
  let d := S.d ++ #[zero, neg cj, mulUp s (subUp cj lo)]
  let G := (Array.ofFn fun a : Fin G.size => (G.getD a.1 #[]).push (if a.1 = j then one else zero))
  ⟨k + 1, c, G, C, d, S.l.push zero, S.u.push up⟩

/-- Whether row `a` has one nonzero entry, equal to `sign`, and its column. -/
private def aux_unitRow (row : Array 𝕋) (sign : 𝕋) : Option ℕ :=
  let nz := (List.range row.size).filter fun i =>
    !(le (row.getD i zero) zero && le zero (row.getD i zero))
  match nz with
  | [i] => if le (row.getD i zero) sign && le sign (row.getD i zero) then some i else none
  | _ => none

/-- The constrained zonotope of a star set (CORA.cpp's `aux_con_zonotope`): `c`, the generators
as rows, `A`, `b`; `none` if the set is empty. -/
private def aux_conZonotope (S : Star 𝕋) :
    Option (Array 𝕋 × Array (Array 𝕋) × Array (Array 𝕋) × Array 𝕋) := Id.run do
  let k := S.k
  -- the rows scaled by their length (as CORA does)
  let norms := S.C.map fun row => sqrtUp 60 (aux_sum (row.toList.map fun v => mulUp v v))
  let C := (S.C.zip norms).map fun (row, nr) => row.map (mulUp nr)
  let d := (S.d.zip norms).map fun (v, nr) => mulUp nr v
  -- the rows that bound one factor give its range; the others stay constraints
  let mut u := S.u
  let mut l := S.l
  let mut bu := Array.replicate k false
  let mut bl := Array.replicate k false
  let mut keep : Array ℕ := #[]
  for a in [0:C.size] do
    let row := C.getD a #[]
    let da := d.getD a zero
    match aux_unitRow row one with
    | some col =>
      u := u.set! col (if bu.getD col false then minimum (u.getD col zero) da else da)
      bu := bu.set! col true
    | none =>
      match aux_unitRow row (neg one) with
      | some col =>
        l := l.set! col (if bl.getD col false then maximum (l.getD col zero) (neg da) else neg da)
        bl := bl.set! col true
      | none => keep := keep.push a
  -- a factor without a value leaves the empty set
  if (List.range k).any fun i => !(le (l.getD i zero) (u.getD i zero)) then return none
  let cen := Array.ofFn fun i : Fin k => mulUp aux_half (addUp (l.getD i.1 zero) (u.getD i.1 zero))
  let R := Array.ofFn fun i : Fin k => mulUp aux_half (subUp (u.getD i.1 zero) (l.getD i.1 zero))
  let c := (Array.range S.c.size).map fun a =>
    (List.range k).foldl
      (fun acc i => addUp acc (mulUp ((S.G.getD a #[]).getD i zero) (cen.getD i zero)))
      (S.c.getD a zero)
  let G := S.G.map fun row =>
    Array.ofFn fun i : Fin k => mulUp (row.getD i.1 zero) (R.getD i.1 zero)
  -- each remaining row C y <= d becomes an equality with a slack factor in [-1, 1]
  let p := keep.size
  let mut A : Array (Array 𝕋) := #[]
  let mut b : Array 𝕋 := #[]
  for r in [0:p] do
    let row := C.getD (keep.getD r 0) #[]
    let (dr, lr, Ar) := (List.range k).foldl (fun (dr, lr, Ar) i =>
      let a := mulUp (row.getD i zero) (R.getD i zero)
      (subUp dr (mulUp (row.getD i zero) (cen.getD i zero)), subUp lr (absolute a), Ar.push a))
      (d.getD (keep.getD r 0) zero, zero, (#[] : Array 𝕋))
    if !(le lr dr) then return none
    b := b.push (mulUp aux_half (addUp lr dr))
    A := A.push (Ar ++ Array.ofFn fun q : Fin p =>
      if q.1 = r then mulUp aux_half (subUp dr lr) else zero)
  -- the generators as rows: the factors', then a zero one per slack
  let gens := (Array.ofFn fun i : Fin k => G.map (·.getD i.1 zero)) ++
    Array.replicate p (Array.replicate S.c.size zero)
  return some (c, gens, A, b)

/-- A matrix of rows of `c` columns as the wire's matrix. -/
private def aux_print (dops : DtypeOps 𝕋) (W : Array (Array 𝕋)) (c : ℕ) : Json :=
  printMat dops.showExact (r := W.size) (c := c)
    (Matrix.of fun i j => (W.getD i.1 #[]).getD j.1 zero)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `neuralNetwork.evaluateConZonotope`: the network on a zonotope without constraints. -/
def evaluateConZonotopeOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "evaluateConZonotope"
  checkFields op req ["layers", "c", "G", "boundApprox"]
  if dops.guaranteed then
    throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the conversion decides on \
      rounded values; use dtype `nearest`"
  else pure ()
  if (fieldOpt req "boundApprox").bind (·.getBool?.toOption) = some false then
    throw s!"{op}: the bounds by linear programs (`boundApprox` false) are not served"
  let ⟨n, c⟩ ← parseVecDyn dops.readExact (← field req "c")
  let dm ← parseMatDyn dops.readExact (← field req "G")
  if dm.r ≠ n then throw s!"{op}: `G` has one row per entry of `c`"
  let gens := Array.ofFn fun l : Fin dm.c => Array.ofFn fun i : Fin dm.r => dm.M i l
  -- the star set through the layers, each ReLU neuron by neuron
  let S ← (← arrField req "layers").foldlM (fun (S : Star 𝕋) L => do
    checkFields op L ["W", "b", "activation"]
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact S.c.size (← field L "W")
    let b ← parseVecFixed dops.readExact m (← field L "b")
    let S := aux_affine (Array.ofFn fun i : Fin m => Array.ofFn (W i)) (Array.ofFn b) S
    match ← strField L "activation" with
    | "relu" => pure ((List.range m).foldl aux_relu S)
    | "identity" => pure S
    | a => throw s!"{op}: the activations are relu or identity, not `{a}`")
    (aux_star (Array.ofFn c) gens)
  match aux_conZonotope S with
  | none => pure [("empty", Json.bool true)]
  | some (c', gens', A, b) =>
    let n' := c'.size
    pure [("empty", Json.bool false), ("c", printVec dops.showExact (n := n') fun i => c'[i]),
      ("G", aux_print dops (Array.ofFn fun a : Fin n' => gens'.map (·.getD a.1 zero)) gens'.size),
      ("A", aux_print dops A (S.k + b.size)),
      ("b", printVec dops.showExact (n := b.size) fun i => b[i])]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
