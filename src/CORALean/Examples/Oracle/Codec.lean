import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Examples.Bench.Rational
import CORALean.Examples.Oracle.Json

/-!
# The wire format: scalars, matrices, intervals, zonotopes

A scalar is `"m*2^e"` (bench's own `--exact` convention), `"m*10^e"`, or a
plain integer read as `m*2^0`; a JSON number is accepted too. `ExactScalar` is
either shape, kept apart rather than merged into `CORALean.Bench.ExactDyadic`:
`m*10^e` at `e < 0` is generally not `m'*2^e'`, `1/50` having no binary
expansion. Both are normalised on the way in as well as the way out: a
precision check reads a mantissa's width literally, so an un-normalised value
could be refused on a width the number it denotes does not need. `"inf"`/`"nan"`
are refused outright; `e ≥ 0` is always accepted, being an integer either way.

A matrix is `{"rows":r,"cols":c,"data":[...]}`, row-major; a vector is the
`cols = 1` case, read straight to `Vec` rather than through `Mat`, which is what
keeps a caller from ever casting between a checked and a discovered dimension.
Every `parse*` below takes the dtype's own checked reader, `String →
ExactScalar → Except String 𝕋`; the `Fixed` ones take a dimension already known
from an earlier field of the request and check the request agrees, the others
read it off the request and return it, as a `Σ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Bench
open Lean (Json)

/-- `a - b`, exact: `Rational.lean` has `add`/`mul`/`neg`, not `sub`. -/
def ExactDyadic.sub (a b : ExactDyadic) : ExactDyadic := a.add b.neg

/-- `a` compared with `b`, exact: the smaller exponent aligned up, as `add` aligns. -/
def ExactDyadic.cmp (a b : ExactDyadic) : Ordering :=
  if a.exponent ≤ b.exponent then
    compare a.mantissa (b.mantissa * 2 ^ (b.exponent - a.exponent).toNat)
  else
    compare (a.mantissa * 2 ^ (a.exponent - b.exponent).toNat) b.mantissa

def ExactDyadic.isZero (a : ExactDyadic) : Bool := a.mantissa = 0

/-- `d`, its every trailing mantissa bit of zero moved into the exponent: `m` odd, or `⟨0,0⟩`
at zero -- run on the way in as well as the way out, see the module docstring for why. -/
def normalizeExact (d : ExactDyadic) : ExactDyadic :=
  if ExactDyadic.isZero d then ⟨0, 0⟩ else
    let (oddAbs, k) := stripTwos d.mantissa.natAbs
    ⟨if d.mantissa < 0 then -(oddAbs : Int) else (oddAbs : Int), d.exponent + (k : Int)⟩

/-- `d`, normalised: `m` odd, or `"0*2^0"` at zero -- every printed binary scalar. -/
def showExactDyadic (d : ExactDyadic) : String :=
  let d := normalizeExact d
  if ExactDyadic.isZero d then "0*2^0" else s!"{d.mantissa}*2^{d.exponent}"


-- ========================================  MAIN TYPE  ========================================= --

/-- A scalar off any grid, from either wire shape: `m*2^e` (`ExactDyadic`) or `m*10^e` at
`e < 0`, generally not a `.dy` -- see the module docstring. `e ≥ 0` normalises to `.dy` either
way, both being the same integer. -/
inductive ExactScalar where
  | dy (d : ExactDyadic)
  | decNeg (m : Int) (d : Nat)  -- `m * 10 ^ (-d)`, `d > 0`, `m` not a multiple of `10`
deriving Repr

def ExactScalar.isZero : ExactScalar → Bool
  | .dy d => ExactDyadic.isZero d
  | .decNeg m _ => m = 0


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_nonFinite (s : String) : Bool := s = "inf" || s = "-inf" || s = "nan" || s = "-nan"

/-- `m`, its every trailing digit of zero dropped, `d` falling by the same count -- fuelled by
`d` itself, which is exactly how many times it can still fall. -/
def aux_stripDecFuel : Nat → Int → Nat → Int × Nat
  | 0, m, d => (m, d)
  | fuel + 1, m, d => if d > 0 ∧ m % 10 = 0 then aux_stripDecFuel fuel (m / 10) (d - 1) else (m, d)

/-- `m * 10 ^ (-d)`, normalised onto `ExactScalar`: `.dy` if the trailing zeros reach `d = 0`
(an integer, `m*10^0 = m*2^0`), `.decNeg` otherwise. -/
def normalizeDecNeg (m : Int) (d : Nat) : ExactScalar :=
  if m = 0 then .dy ⟨0, 0⟩ else
    let (m', d') := aux_stripDecFuel d m d
    if d' = 0 then .dy ⟨m', 0⟩ else .decNeg m' d'

/-- `m * 10 ^ e` at `e ≥ 0`, onto `ExactScalar`: always `.dy`, `10^e = 5^e * 2^e` folded into
the mantissa and the exponent left as `e`. -/
def aux_mkDecimal (m e : Int) : ExactScalar :=
  if e ≥ 0 then .dy (normalizeExact ⟨m * 5 ^ e.toNat, e⟩) else normalizeDecNeg m (-e).toNat

def parseScalarStr (s : String) : Except String ExactScalar :=
  if aux_nonFinite s then throw s!"`{s}` is not a finite scalar" else
  match s.splitOn "*2^" with
  | [m, e] => match String.toInt? m, String.toInt? e with
    | some mi, some ei => pure (.dy (normalizeExact ⟨mi, ei⟩))
    | _, _ => throw s!"`{s}` is not `m*2^e` with integer `m`, `e`"
  | _ => match s.splitOn "*10^" with
    | [m, e] => match String.toInt? m, String.toInt? e with
      | some mi, some ei => pure (aux_mkDecimal mi ei)
      | _, _ => throw s!"`{s}` is not `m*10^e` with integer `m`, `e`"
    | _ => match String.toInt? s with
      | some mi => pure (.dy ⟨mi, 0⟩)
      | none => throw s!"`{s}` is not an integer, `m*2^e` or `m*10^e`"

/-- A JSON number, onto `ExactScalar` -- exact iff `JsonNumber`'s decimal mantissa
is a multiple of its own power of ten; always `.dy`, being an integer. -/
def parseScalarNum (n : Lean.JsonNumber) : Except String ExactScalar :=
  let den : Int := 10 ^ n.exponent
  if n.mantissa % den = 0 then pure (.dy (normalizeExact ⟨n.mantissa / den, 0⟩))
  else throw s!"{n.mantissa}e-{n.exponent} is not an integer"

/-- A scalar off any grid, from either wire shape -- a string or a JSON number -- normalised. -/
def parseScalar : Json → Except String ExactScalar
  | .str s => parseScalarStr s
  | .num n => parseScalarNum n
  | j => throw s!"scalar must be a string `m*2^e`/`m*10^e` or an integer, not {kindOf j}"

/-- `j`'s field `name`, as an off-grid scalar, the field named on failure. -/
def scalarField (j : Json) (name : String) : Except String ExactScalar := do
  match parseScalar (← field j name) with
  | .ok d => pure d
  | .error e => throw s!"field `{name}`: {e}"

/-- `v`, for a message -- not the output grammar (`Dtype.lean`'s `showExact`), only for naming
what a request sent. -/
def showScalarForMessage : ExactScalar → String
  | .dy d => showExactDyadic d
  | .decNeg m d => s!"{m}*10^-{d}"


/-- A matrix whose shape is a runtime value, read off the request rather than fixed by
the caller -- `Mat 𝕋 r c`'s own `r`, `c` alongside it. -/
structure DynMat (𝕋 : Type) where
  r : Nat
  c : Nat
  M : Mat 𝕋 r c

/-- A zonotope whose dimension `n` is a runtime value -- `Σ n, Zonotope (Vec 𝕋 n)`, named. -/
structure DynZonotope (𝕋 : Type) where
  n : Nat
  Z : Zonotope (Vec 𝕋 n)

/-- A matrix of off-grid scalars, row-major and flat -- `roundTo`'s one exception to "every
input is exactly representable", so no `readD` and no `Mat` (which would ask a `FloatOps`
instance of `ExactDyadic`, which does not exist and should not). -/
structure DynMatScalar where
  r : Nat
  c : Nat
  data : Array ExactScalar

/-- `j` as a `DynMatScalar` -- `parseMatDyn`'s shape check, `parseScalar` in place of `readD`. -/
def parseMatScalarDyn (j : Json) : Except String DynMatScalar := do
  let r ← natField j "rows"
  let c ← natField j "cols"
  let raw ← arrField j "data"
  if raw.size ≠ r * c then
    throw s!"matrix `data` has {raw.size} entries, expected rows*cols = {r * c}"
  let vals ← raw.mapIdxM fun i v => match parseScalar v with
    | .ok d => pure d
    | .error e => throw s!"data[{i}]: {e}"
  pure ⟨r, c, vals⟩

/-- A zonotope of off-grid scalars, the same exception at every one of its four arrays. -/
structure DynZonotopeScalar where
  n : Nat
  h : Nat
  c : Array ExactScalar
  G : Array ExactScalar
  Einf : Array ExactScalar
  Esup : Array ExactScalar

/-- `{"c":Mat(n,1),"G":Mat(n,h),"E":Interval(n,1)}`, every entry left off-grid. -/
def parseZonotopeScalar (j : Json) : Except String DynZonotopeScalar := do
  let cM ← parseMatScalarDyn (← field j "c")
  if cM.c ≠ 1 then throw s!"zonotope `c` must be n×1, not {cM.r}×{cM.c}"
  let n := cM.r
  let gM ← parseMatScalarDyn (← field j "G")
  if gM.r ≠ n then throw s!"zonotope `G` has {gM.r} rows, expected {n} (from `c`)"
  let eJ ← field j "E"
  let infM ← parseMatScalarDyn (← field eJ "inf")
  let supM ← parseMatScalarDyn (← field eJ "sup")
  if infM.r ≠ n ∨ infM.c ≠ 1 ∨ supM.r ≠ n ∨ supM.c ≠ 1 then
    throw s!"zonotope `E` must be {n}×1, not {infM.r}×{infM.c} / {supM.r}×{supM.c}"
  pure ⟨n, gM.c, cM.data, gM.data, infM.data, supM.data⟩

variable {𝕋 : Type} [FloatOps 𝕋] (readD : String → ExactScalar → Except String 𝕋)

/-- `vals`, row-major, as an `r × c` matrix -- shared by every `parseMat*` below. -/
def aux_mkMat (r c : Nat) (vals : Array 𝕋) : Mat 𝕋 r c :=
  Matrix.of fun (i : Fin r) (l : Fin c) => vals.getD (i.val * c + l.val) FloatOps.zero

/-- Every entry of `data`, read through `readD`, the field name of `data[i]` on failure. -/
def aux_parseData (data : Array Json) : Except String (Array 𝕋) :=
  data.mapIdxM fun i v => do
    match parseScalar v with
    | .error e => throw s!"data[{i}]: {e}"
    | .ok d => readD s!"data[{i}]" d

/-- `j` as a column vector, `n` read off `rows` -- `cols` must be `1`. -/
def parseVec (j : Json) : Except String (Σ n : Nat, Vec 𝕋 n) := do
  let r ← natField j "rows"
  let c ← natField j "cols"
  if c ≠ 1 then throw s!"expected a column vector (cols = 1), got cols = {c}"
  let vals ← aux_parseData readD (← arrField j "data")
  if vals.size ≠ r then throw s!"vector `data` has {vals.size} entries, expected rows = {r}"
  pure ⟨r, fun i => vals.getD i.val FloatOps.zero⟩

/-- `j` as a column vector of the already-known length `n`. -/
def parseVecFixed (n : Nat) (j : Json) : Except String (Vec 𝕋 n) := do
  let r ← natField j "rows"
  let c ← natField j "cols"
  if r ≠ n ∨ c ≠ 1 then throw s!"expected a {n}×1 column vector, got {r}×{c}"
  let vals ← aux_parseData readD (← arrField j "data")
  if vals.size ≠ n then throw s!"vector `data` has {vals.size} entries, expected {n}"
  pure fun i => vals.getD i.val FloatOps.zero

/-- `j` as a matrix, both `rows` and `cols` read off the request. -/
def parseMatDyn (j : Json) : Except String (DynMat 𝕋) := do
  let r ← natField j "rows"
  let c ← natField j "cols"
  let vals ← aux_parseData readD (← arrField j "data")
  if vals.size ≠ r * c then
    throw s!"matrix `data` has {vals.size} entries, expected rows*cols = {r * c}"
  pure ⟨r, c, aux_mkMat r c vals⟩

/-- `j` as a matrix with the already-known column count `c` -- `rows` read off the request. -/
def parseMatColsFixed (c : Nat) (j : Json) : Except String (Σ r : Nat, Mat 𝕋 r c) := do
  let r ← natField j "rows"
  let jc ← natField j "cols"
  if jc ≠ c then throw s!"matrix has {jc} columns, expected {c}"
  let vals ← aux_parseData readD (← arrField j "data")
  if vals.size ≠ r * c then
    throw s!"matrix `data` has {vals.size} entries, expected rows*cols = {r * c}"
  pure ⟨r, aux_mkMat r c vals⟩

/-- `j` as a matrix with the already-known row count `r` -- `cols` read off the request:
CORA's generator matrix, `n` fixed and `h` discovered. -/
def parseMatRowsFixed (r : Nat) (j : Json) : Except String (Σ c : Nat, Mat 𝕋 r c) := do
  let jr ← natField j "rows"
  let c ← natField j "cols"
  if jr ≠ r then throw s!"matrix has {jr} rows, expected {r}"
  let vals ← aux_parseData readD (← arrField j "data")
  if vals.size ≠ r * c then
    throw s!"matrix `data` has {vals.size} entries, expected rows*cols = {r * c}"
  pure ⟨c, aux_mkMat r c vals⟩

/-- `{"inf":Mat,"sup":Mat}` at the already-known length `n`. -/
def parseIntervalVecFixed (n : Nat) (j : Json) : Except String (Interval (Vec 𝕋 n)) := do
  pure ⟨← parseVecFixed readD n (← field j "inf"),
    ← parseVecFixed readD n (← field j "sup")⟩

/-- `{"inf":Mat,"sup":Mat}`, both `m × n`, `n` already known and `m` discovered --
refused if `inf` and `sup` disagree on `m`. -/
def parseIntervalMatColsFixed (n : Nat) (j : Json) :
    Except String (Σ m : Nat, Interval (Mat 𝕋 m n)) := do
  let ⟨m₁, lo⟩ ← parseMatColsFixed readD n (← field j "inf")
  let ⟨m₂, hi⟩ ← parseMatColsFixed readD n (← field j "sup")
  if h : m₁ = m₂ then pure ⟨m₁, ⟨lo, h ▸ hi⟩⟩
  else throw s!"interval `inf` has {m₁} rows but `sup` has {m₂}"

/-- `{"c":Mat(n,1),"G":Mat(n,h),"E":Interval(n,1)}`, `n` read off `c`. -/
def parseZonotope (j : Json) : Except String (DynZonotope 𝕋) := do
  let ⟨n, cVec⟩ ← parseVec readD (← field j "c")
  let ⟨h, gMat⟩ ← parseMatRowsFixed readD n (← field j "G")
  let eBox ← parseIntervalVecFixed readD n (← field j "E")
  pure ⟨n, { h := h, c := cVec, G := fun j i => gMat i j, I_error := eBox }⟩

/-- The same, at an already-known `n` -- the second zonotope of a two-operand op. -/
def parseZonotopeFixed (n : Nat) (j : Json) : Except String (Zonotope (Vec 𝕋 n)) := do
  let cVec ← parseVecFixed readD n (← field j "c")
  let ⟨h, gMat⟩ ← parseMatRowsFixed readD n (← field j "G")
  let eBox ← parseIntervalVecFixed readD n (← field j "E")
  pure { h := h, c := cVec, G := fun j i => gMat i j, I_error := eBox }

variable (showD : 𝕋 → String)

-- The printers, the reverse of every `parse*` above: `showD` on every entry, nested the same way.
def printVec {n : Nat} (v : Vec 𝕋 n) : Json :=
  Json.mkObj
    [ ("rows", Lean.toJson n), ("cols", Lean.toJson (1 : Nat)),
      ("data", Json.arr (Array.ofFn fun i : Fin n => Json.str (showD (v i)))) ]

def printMat {r c : Nat} (M : Mat 𝕋 r c) : Json :=
  Json.mkObj
    [ ("rows", Lean.toJson r), ("cols", Lean.toJson c),
      ("data", Json.arr ((Array.ofFn fun i : Fin r =>
        Array.ofFn fun l : Fin c => Json.str (showD (M i l))).flatten)) ]

def printIntervalVec {n : Nat} (I : Interval (Vec 𝕋 n)) : Json :=
  Json.mkObj [("inf", printVec showD I.inf), ("sup", printVec showD I.sup)]

def printIntervalMat {r c : Nat} (I : Interval (Mat 𝕋 r c)) : Json :=
  Json.mkObj [("inf", printMat showD I.inf), ("sup", printMat showD I.sup)]

def printZonotope {n : Nat} (Z : Zonotope (Vec 𝕋 n)) : Json :=
  Json.mkObj
    [("c", printVec showD Z.c), ("G", printMat showD fun i j => Z.G j i),
      ("E", printIntervalVec showD Z.I_error)]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
