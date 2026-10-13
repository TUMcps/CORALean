import CORALean.Examples.Bench.Rational

/-!
# Reading a converted MNIST network and its test images

Two flat, whitespace-separated text formats, both produced by
`experiments/nn/mnist/*.py` (see `SOURCES.md` for the exact commands and
checksums) and read back here with nothing but `String` splitting and
`Nat`/`Int` parsing -- no JSON, no external library, so a reader never needs
more than this file to regenerate a network or a data point by hand.

`decodeFloat32` is the one place a bit pattern becomes a number: sign, an
8-bit exponent and a 23-bit mantissa, read into `ExactDyadic` exactly --
subnormals scaled by `2^-149` rather than `2^(e-150)`, and `NaN`/`±Inf`
(exponent `0xFF`) rejected outright, since nothing downstream is prepared to
propagate one. Every weight and bias in `experiments/nn/mnist/nets/` is
`onnx`'s own `float32`, so this is the *only* place rounding could silently
happen and doesn't: the returned `ExactDyadic` is the bit pattern's exact
value, read into whichever scalar a run picks only afterwards, in
`MnistNetwork.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench.Mnist

/-! ## Tokenizing

Both file formats are whitespace-separated only: no format cares which
whitespace character (space or newline) separates two tokens, so a reader
maps every newline to a space first and splits on that alone. -/

def tokenize (s : String) : Array String :=
  ((s.map fun c => if c = '\n' ∨ c = '\r' ∨ c = '\t' then ' ' else c).splitOn " ").toArray.filter
    (·.length > 0)

/-- A cursor into an already-tokenized file: `next` reads one token and
advances, so a parser threads `TokStream` the way `Config.lean` threads
`Json`, rather than pattern-matching a `List` by hand. -/
structure TokStream where
  toks : Array String
  pos : Nat := 0

def TokStream.ofString (s : String) : TokStream := ⟨tokenize s, 0⟩

def TokStream.next (t : TokStream) : Except String (String × TokStream) :=
  if h : t.pos < t.toks.size then pure (t.toks[t.pos], { t with pos := t.pos + 1 })
  else throw "unexpected end of input"

def TokStream.nextNat (t : TokStream) : Except String (Nat × TokStream) := do
  let (s, t') ← t.next
  match s.toNat? with
  | some n => pure (n, t')
  | none => throw s!"`{s}` is not a natural number"


/-! ## Float32 bit patterns -/

def hexDigit (c : Char) : Except String UInt32 :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat.toUInt32 - '0'.toNat.toUInt32)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat.toUInt32 - 'a'.toNat.toUInt32 + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat.toUInt32 - 'A'.toNat.toUInt32 + 10)
  else throw s!"`{c}` is not a hex digit"

/-- An 8-hex-digit token as the `UInt32` it spells, most significant digit
first -- `convert_onnx.py`'s own `float32_hex`, read back. -/
def parseHex32 (s : String) : Except String UInt32 := do
  if s.length ≠ 8 then throw s!"`{s}` is not an 8-hex-digit float32 bit pattern" else
  let digits ← s.toList.mapM hexDigit
  pure (digits.foldl (fun acc d => acc * 16 + d) 0)

/-- The exact value a binary32 bit pattern denotes: `± m · 2^e`, `m` restoring
the implicit leading `1` for a normal number, `2^-149` the subnormal scale.
Fails on `NaN`/`±Inf` (exponent field `0xFF`). -/
def decodeFloat32 (bits : UInt32) : Except String ExactDyadic :=
  let sign := (bits >>> 31) &&& 1
  let expBits := (bits >>> 23) &&& 0xFF
  let mant := bits &&& 0x7FFFFF
  if expBits = 0xFF then throw "float32 bit pattern is NaN or ±Inf, not finite" else
  let (m, e) : UInt32 × Int :=
    if expBits = 0 then (mant, -149) else (0x800000 ||| mant, (expBits.toNat : Int) - 150)
  pure ⟨if sign = 1 then -(m.toNat : Int) else (m.toNat : Int), e⟩

/-- `parseHex32` then `decodeFloat32`, the pair every weight and bias token goes through. -/
def parseFloat32 (s : String) : Except String ExactDyadic := do decodeFloat32 (← parseHex32 s)

def TokStream.nextFloat32 (t : TokStream) : Except String (ExactDyadic × TokStream) := do
  let (s, t') ← t.next
  pure (← parseFloat32 s, t')


/-! ## The network file: `<numLayers> <inputDim> (<outDim> <inDim> <relu> W... b...)*` -/

/-- One `Gemm` (`+ Relu`, but for the last): `W` stored row-major, `outDim`
rows of `inDim` entries; `relu` is whether a `Relu` node follows in the
original graph -- `false` only for the very last layer. -/
structure MnistAffine where
  outDim : Nat
  inDim : Nat
  relu : Bool
  W : Array (Array ExactDyadic)
  b : Array ExactDyadic

structure MnistNet where
  inputDim : Nat
  layers : Array MnistAffine


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- one weight row, `inDim` hex tokens
def aux_parseRow (inDim : Nat) (t : TokStream) :
    Except String (Array ExactDyadic × TokStream) := do
  let mut t := t
  let mut row := #[]
  for _ in [0:inDim] do
    let (x, t') ← t.nextFloat32
    t := t'
    row := row.push x
  pure (row, t)

-- dims and the relu flag, then `outDim` rows of `W` and one row of `b`
def aux_parseLayer (t : TokStream) : Except String (MnistAffine × TokStream) := do
  let (outDim, t) ← t.nextNat
  let (inDim, t) ← t.nextNat
  let (reluTok, t) ← t.next
  let relu ← match reluTok with
    | "0" => pure false
    | "1" => pure true
    | other => throw s!"`{other}` is not `0` or `1` for a layer's relu flag"
  let mut t := t
  let mut rows := #[]
  for _ in [0:outDim] do
    let (row, t') ← aux_parseRow inDim t
    t := t'
    rows := rows.push row
  let (b, t2) ← aux_parseRow outDim t
  pure (⟨outDim, inDim, relu, rows, b⟩, t2)

/-- Each layer's `inDim` is the previous one's `outDim`, and only the last
layer's `relu` is `false` -- checked once so a scrambled file fails with a
message rather than quietly computing something other than `mnistfc`. -/
def aux_checkShape (net : MnistNet) : Except String Unit := do
  let mut expected := net.inputDim
  for h : i in [0:net.layers.size] do
    let l := net.layers[i]
    if l.inDim ≠ expected then
      throw s!"layer {i}: expected input dimension {expected}, file has {l.inDim}"
    if l.relu = (i = net.layers.size - 1) then
      throw s!"layer {i}: relu flag `{l.relu}` is wrong for a {
        if i = net.layers.size - 1 then "last" else "non-last"} layer"
    expected := l.outDim
  pure ()


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Parses a whole network file: `MnistParse.lean`'s module docstring gives the
exact format, `convert_onnx.py`'s the reason it looks that way. -/
def parseMnistNet (contents : String) : Except String MnistNet := do
  let t := TokStream.ofString contents
  let (numLayers, t) ← t.nextNat
  let (inputDim, t) ← t.nextNat
  let mut t := t
  let mut layers := #[]
  for _ in [0:numLayers] do
    let (l, t') ← aux_parseLayer t
    t := t'
    layers := layers.push l
  let net : MnistNet := ⟨inputDim, layers⟩
  aux_checkShape net
  pure net

/-- One converted MNIST image: its label and its 784 raw pixel values,
`0`..`255`, row-major -- `experiments/nn/mnist/fetch_mnist.py`'s own format. -/
structure MnistImage where
  label : Nat
  pixels : Array Nat

def aux_parsePixel (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => if n < 256 then pure n else throw s!"pixel `{n}` is not a byte"
  | none => throw s!"`{s}` is not a pixel byte"

/-- One data line: `label` then 784 decimal pixel bytes. -/
def aux_parseImageLine (line : String) : Except String MnistImage := do
  let toks := ((line.splitOn " ").filter (·.length > 0)).toArray
  if toks.size ≠ 785 then throw s!"data line has {toks.size} tokens, expected 785" else
  let label ← match toks[0]!.toNat? with
    | some n => pure n
    | none => throw s!"`{toks[0]!}` is not a label"
  let pixels ← (toks.extract 1 785).mapM aux_parsePixel
  pure ⟨label, pixels⟩

/-- Parses `mnist_test_first100.txt`: one line per image, `label` then 784
decimal pixel bytes. -/
def parseMnistData (contents : String) : Except String (Array MnistImage) :=
  let lines := (contents.splitOn "\n").filter (·.length > 0)
  lines.toArray.mapM aux_parseImageLine

end CORALean.Bench.Mnist


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
