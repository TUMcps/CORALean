import CORALean.Global.Float.Sqrt
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The regions of an activation's polynomials: CORA's findRegionPolys of a ReLU

CORA.cpp's `find_region_polys` at `nearest`, operation by operation: from `lMax` up, a region's
upper end is halved until the regression fit of the order is within `tol` (then lower orders down
to a constant), from `uMax` down its lower end. A fit is CORA.cpp's `priv_approx_poly` at
`regression`: `10 (k + 1)` equidistant points, the Vandermonde matrix by repeated products,
Householder's least squares, then the ReLU's error (the extremes of `p` on `[l, 0]` and of `p - x`
on `[0, u]`, at the ends and the bisected roots of the derivative), the polynomial moved by its
middle. Only the ReLU: arithmetic and `sqrt`, no libm function. The reply is the regions between
the outer two, sorted; `nearest` only, the regions being decisions on rounded values.

## Inputs
* `dops` – dtype operations
* `op` – op name, without the prefix
* `req` – request

## Output
* the op's reply
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float FloatOps
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `a < b` and `a == b` as C++ compares doubles. -/
private def aux_lt (a b : 𝕋) : Bool := le a b && !(le b a)
private def aux_eq (a b : 𝕋) : Bool := le a b && le b a

/-- `std::min(a, b)` and `std::max(a, b)`: `b < a ? b : a` and `a < b ? b : a`. -/
private def aux_min (a b : 𝕋) : 𝕋 := if aux_lt b a then b else a
private def aux_max (a b : 𝕋) : 𝕋 := if aux_lt a b then b else a

/-- The constants of the fit, exact in the dtype. -/
private structure Consts (𝕋 : Type) where
  half : 𝕋
  two : 𝕋
  nat : ℕ → 𝕋

/-- CORA.cpp's `priv_polyval`: Horner from `0`, the highest power first. -/
private def aux_polyval (p : Array 𝕋) (x : 𝕋) : 𝕋 :=
  p.foldl (fun v c => addUp (mulUp v x) c) zero

/-- `aux_derivative`: `p[i] (n - 1 - i)`, the constant `0` for a constant. -/
private def aux_derivative (C : Consts 𝕋) (p : Array 𝕋) : Array 𝕋 :=
  let n := p.size
  let out := (Array.range (n - 1)).map fun i => mulUp (p.getD i zero) (C.nat (n - 1 - i))
  if out.isEmpty then #[zero] else out

/-- `aux_roots`: the real roots of `p` in `[a, b]`; the roots of `p'` cut `[a, b]` into monotone
pieces and a piece with a sign change is bisected (200 rounds at most). `fuel` bounds the degree. -/
private def aux_roots (C : Consts 𝕋) : ℕ → Array 𝕋 → 𝕋 → 𝕋 → Array 𝕋
  | 0, _, _, _ => #[]
  | fuel + 1, p₀, a, b => Id.run do
    -- the leading zeros dropped
    let mut p := p₀
    while p.size > 1 && aux_eq (p.getD 0 zero) zero do p := p.extract 1 p.size
    if p.size ≤ 1 then return #[]
    if p.size = 2 then
      let r := divUp (neg (p.getD 1 zero)) (p.getD 0 zero)
      return if le a r && le r b then #[r] else #[]
    -- the pieces between the ends and the roots of the derivative
    let pieces := #[a] ++ aux_roots C fuel (aux_derivative C p) a b ++ #[b]
    let mut out : Array 𝕋 := #[]
    for i in [0:pieces.size - 1] do
      let mut lo := pieces.getD i zero
      let mut hi := pieces.getD (i + 1) zero
      let fLo := aux_polyval p lo
      let fHi := aux_polyval p hi
      if aux_eq fLo zero then out := out.push lo
      if le zero (mulUp fLo fHi) then continue
      -- the sign change bisected until the ends meet
      for _ in [0:200] do
        let mid := addUp lo (mulUp (subUp hi lo) C.half)
        if le mid lo || le hi mid then break
        if aux_lt zero (mulUp (aux_polyval p mid) fLo) then lo := mid else hi := mid
      out := out.push (addUp lo (mulUp (subUp hi lo) C.half))
    if aux_eq (aux_polyval p b) zero then out := out.push b
    return out

/-- `aux_range`: the least and largest value of `p` at `a`, `b` and the roots of `p'`. -/
private def aux_range (C : Consts 𝕋) (p : Array 𝕋) (a b : 𝕋) : 𝕋 × 𝕋 :=
  let points := #[a, b] ++ aux_roots C (p.size + 1) (aux_derivative C p) a b
  let v₀ := aux_polyval p a
  points.foldl (fun (lo, hi) x => (aux_min lo (aux_polyval p x), aux_max hi (aux_polyval p x)))
    (v₀, v₀)

/-- `aux_min_max_diff`: the range of `p1 - p2` over `[a, b]`, the shorter one padded in front. -/
private def aux_minMaxDiff (C : Consts 𝕋) (p1 p2 : Array 𝕋) (a b : 𝕋) : 𝕋 × 𝕋 :=
  let n := max p1.size p2.size
  let o1 := n - p1.size
  let o2 := n - p2.size
  let p := Array.ofFn fun i : Fin n =>
    let x := if o1 ≤ i.1 then p1.getD (i.1 - o1) zero else zero
    if o2 ≤ i.1 then subUp x (p2.getD (i.1 - o2) zero) else x
  aux_range C p a b

/-- `aux_relu_error`: the ReLU's error radius, the polynomial moved by the middle. -/
private def aux_reluError (C : Consts 𝕋) (p : Array 𝕋) (l u : 𝕋) : Array 𝕋 × 𝕋 :=
  let (lo1, hi1) := aux_minMaxDiff C p #[zero, zero] l zero
  let (lo2, hi2) := aux_minMaxDiff C p #[one, zero] zero u
  let lo := aux_min lo1 lo2
  let hi := aux_max hi1 hi2
  let mid := divUp (addUp hi lo) C.two
  (p.modify (p.size - 1) (subUp · mid), subUp hi mid)

/-- `aux_solve`: least squares of the columns `A` (the last one the right-hand side) by
Householder's reflections, then back substitution; `k` unknowns. -/
private def aux_solve (C : Consts 𝕋) (p : ℕ) (k : ℕ) (A₀ : Array (Array 𝕋)) : Array 𝕋 :=
  Id.run do
    let rows := (A₀.getD 0 #[]).size
    let mut A := A₀
    for j in [0:min k rows] do
      -- the reflection that clears the column `j` below the diagonal
      let col := A.getD j #[]
      let norm := sqrtUp p ((List.range' j (rows - j)).foldl
        (fun s i => addUp s (mulUp (col.getD i zero) (col.getD i zero))) zero)
      if aux_eq norm zero then continue
      let ajj := col.getD j zero
      let v := (Array.range rows).map fun i =>
        if i < j then zero
        else if i = j then subUp ajj (if aux_lt zero ajj then neg norm else norm)
        else col.getD i zero
      let vv := (List.range' j (rows - j)).foldl
        (fun s i => addUp s (mulUp (v.getD i zero) (v.getD i zero))) zero
      if aux_eq vv zero then continue
      -- applied to the columns `j..` and to the right-hand side
      for c in [j:k + 1] do
        let x := A.getD c #[]
        let dot := (List.range' j (rows - j)).foldl
          (fun s i => addUp s (mulUp (v.getD i zero) (x.getD i zero))) zero
        let f := divUp (mulUp C.two dot) vv
        A := A.set! c ((Array.range rows).map fun i =>
          if i < j then x.getD i zero else subUp (x.getD i zero) (mulUp f (v.getD i zero)))
    -- back substitution
    let b := A.getD k #[]
    let mut sol : Array 𝕋 := Array.replicate k zero
    for j' in [0:min k rows] do
      let j := min k rows - 1 - j'
      let s := (List.range' (j + 1) (k - (j + 1))).foldl
        (fun s c => subUp s (mulUp ((A.getD c #[]).getD j zero) (sol.getD c zero))) (b.getD j zero)
      let d := (A.getD j #[]).getD j zero
      sol := sol.set! j (if aux_eq d zero then zero else divUp s d)
    return sol

/-- `aux_fit` at `regression`: the ReLU at `10 (k + 1)` equidistant points of `[l, u]` (the last
exactly `u`), the Vandermonde columns `x^k .. x^0` by repeated products, least squares. -/
private def aux_fit (C : Consts 𝕋) (l u : 𝕋) (k : ℕ) : Array 𝕋 :=
  let m := 10 * (k + 1)
  let step := divUp (subUp u l) (C.nat (m - 1))
  let xs := (Array.range m).map fun i => if i + 1 = m then u else addUp l (mulUp (C.nat i) step)
  let ys := xs.map fun x => if aux_lt x zero then zero else x
  -- column `j` holds the power `k - j`: `1`, then a product by `x` per power
  let powers := xs.map fun x =>
    (List.range k).foldl (fun acc _ => acc.push (mulUp (acc.getD (acc.size - 1) one) x)) #[one]
  let cols := (Array.range (k + 1)).map fun j => powers.map fun pw => pw.getD (k - j) zero
  aux_solve C 60 (k + 1) (cols.push ys)

/-- CORA.cpp's `priv_approx_poly` of the ReLU at `regression`: the linear pieces exactly, else the
fit and its error. -/
private def aux_approxPoly (C : Consts 𝕋) (l u : 𝕋) (k : ℕ) : Array 𝕋 × 𝕋 :=
  if le u zero then (#[zero, zero], zero)
  else if le zero l then (#[one, zero], zero)
  else aux_reluError C (aux_fit C l u k) l u

/-- A region `[l, u]` with its polynomial and radius. -/
private abbrev Region (𝕋 : Type) := 𝕋 × 𝕋 × Array 𝕋 × 𝕋

/-- The fit of order `k` on `[l, u]`, then lower orders down to `0` while below `tol`. -/
private def aux_lower (C : Consts 𝕋) (tol l u : 𝕋) (k : ℕ) (fit : Array 𝕋 × 𝕋) :
    Array 𝕋 × 𝕋 := Id.run do
  let mut best := fit
  for i in [0:k] do
    let lower := aux_approxPoly C l u (k - 1 - i)
    if le tol lower.2 then break
    best := lower
  return best

/-- From below: the upper end halved until the fit is within `tol` (CORA.cpp's first inner loop). -/
private def aux_fromBelow (C : Consts 𝕋) (op : String) (tol l u : 𝕋) (k : ℕ) :
    Except String (𝕋 × Array 𝕋 × 𝕋) := do
  let mut ui := u
  let mut fit := aux_approxPoly C l ui k
  let mut fuel := 4096
  while aux_lt tol fit.2 do
    if fuel = 0 then throw s!"{op}: the halving did not stop"
    fuel := fuel - 1
    ui := addUp l (mulUp (subUp ui l) C.half)
    if aux_lt (subUp ui l) tol then throw s!"{op}: no polynomial (CORA:notConverged)"
    fit := aux_approxPoly C l ui k
  pure (ui, aux_lower C tol l ui k fit)

/-- From above: the lower end halved the same way, the error computed again on the fit. -/
private def aux_fromAbove (C : Consts 𝕋) (op : String) (tol l u : 𝕋) (k : ℕ) :
    Except String (𝕋 × Array 𝕋 × 𝕋) := do
  let again (li : 𝕋) := aux_reluError C (aux_approxPoly C li u k).1 li u
  let mut li := l
  let mut fit := again li
  let mut fuel := 4096
  while aux_lt tol fit.2 do
    if fuel = 0 then throw s!"{op}: the halving did not stop"
    fuel := fuel - 1
    li := subUp u (divUp (subUp u li) C.two)
    if aux_lt (subUp u li) tol then throw s!"{op}: no polynomial (CORA:notConverged)"
    fit := again li
  pure (li, fit)

/-- CORA.cpp's outer loop: a region from below, then one from above, until they meet. -/
private def aux_regions (C : Consts 𝕋) (op : String) (tol lMax uMax : 𝕋) (k : ℕ) :
    Except String (Array (Region 𝕋)) := do
  let mut l := lMax
  let mut u := uMax
  let mut below : Array (Region 𝕋) := #[]
  let mut above : Array (Region 𝕋) := #[]
  let mut fuel := 100000
  while aux_lt l u do
    if fuel = 0 then throw s!"{op}: the regions did not close"
    fuel := fuel - 1
    let (ui, p, d) ← aux_fromBelow C op tol l u k
    below := below.push (l, ui, p, d)
    l := ui
    if aux_eq l u then break
    let (li, p, d) ← aux_fromAbove C op tol l u k
    above := above.push (li, u, p, d)
    u := li
  pure (below ++ above.reverse)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `nnLayer.` from this file, run; `none` for a name it does not serve. -/
@[noinline, nospecialize]
def handleNnRegionOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "findRegionPolys" => some (do
    checkFields op req ["activation", "tol", "order", "lMax", "uMax"]
    if dops.guaranteed then
      throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the regions are \
        decisions on rounded values; use dtype `nearest`"
    let act ← strField req "activation"
    if act ≠ "relu" then throw s!"{op}: `activation` relu only (sigmoid and tanh take libm)"
    let k ← natField req "order"
    if k = 0 then throw s!"{op}: `order` is at least 1"
    let tol ← dops.readExact "tol" (← scalarField req "tol")
    let lMax ← dops.readExact "lMax" (← scalarField req "lMax")
    let uMax ← dops.readExact "uMax" (← scalarField req "uMax")
    if !(aux_lt zero tol) || !(aux_lt lMax uMax) then
      throw s!"{op}: tol > 0 and lMax < uMax"
    let nat (i : ℕ) : 𝕋 := (dops.readExact "count" (.dy ⟨i, 0⟩)).toOption.getD zero
    let C : Consts 𝕋 := ⟨← dops.readExact "half" (.dy ⟨1, -1⟩), nat 2, nat⟩
    -- the regions, each with its polynomial and radius
    let R ← aux_regions C op tol lMax uMax k
    pure [("regions", Json.arr (R.map fun (l, u, p, d) => Json.mkObj [
      ("l", Json.str (dops.showExact l)), ("u", Json.str (dops.showExact u)),
      ("p", printVec dops.showExact (fun i : Fin p.size => p[i])),
      ("d", Json.str (dops.showExact d))]))])
  | _ => none

/-- Every op of `nnLayer.` this file serves, without the prefix. -/
def nnRegionOpNames : List String := [ "findRegionPolys" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
