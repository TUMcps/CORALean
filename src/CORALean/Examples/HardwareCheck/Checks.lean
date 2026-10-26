import CORALean.Examples.HardwareCheck.Rng
import CORALean.Examples.Bench.OpCompareCodec
import CORALean.Examples.HardwareCheck.Exact
import CORALean.Global.Float.Instances.Binary64.Operations.Half
import CORALean.Global.Float.Instances.Binary64.Operations.Basic

/-!
# The checks

One function per conjunct of `IsTrustedHardware`, each comparing the native result with the exact
one and answering with the failures it saw, tagged by kind: `unsound` (the result lies on the wrong
side of the exact value, or a `≤` that holds natively while the decoded values disagree), `loose`
(more than one step past the soft-float's directed result, or a `≤` that fails natively while the
decoded values are ordered), `range` (NaN where the result is in the normal range, or a number
where it is not) and `value` (a result that is not what the operation must return). A `Stat` counts
them per operation and keeps the first failing input's report.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.HardwareCheck

open CORALean.Float CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A failure: its kind and the report line. -/
abbrev Fail := String × String

private def aux_hex (b : UInt64) : String := uint64ToHex b

private def aux_hexF (f : Float) : String := uint64ToHex f.toBits

private def aux_soft (x : IEEE IEEEFormat.binary64) : String :=
  match bitsOf x with
  | some b => uint64ToHex b
  | none => "overflow"

private def aux_expect (o : Option UInt64) : String :=
  match o with
  | some b => uint64ToHex b
  | none => "nan"

private def aux_nan (f : Float) : Bool := f.isNaN


-- ========================================  MAIN TYPE  ========================================= --

/-- Per operation: samples, those the model puts outside the normal range, of those how many make
the axiom's own inequality false as stated, and the failures by kind. -/
structure Stat where
  name : String
  n : Nat := 0
  outOfRange : Nat := 0
  literalFalse : Nat := 0
  unsound : Nat := 0
  loose : Nat := 0
  range : Nat := 0
  value : Nat := 0
  first : Option String := none

/-- The result of one sample. -/
structure Outcome where
  fails : List Fail := []
  out : Bool := false
  literalFalse : Bool := false

/-- Adds one sample's outcome to the tally: the sample count, the out-of-range and literally false
counts, the failures by kind, and the first failure message. -/
def Stat.add (s : Stat) (o : Outcome) : Stat :=
  let count k := (o.fails.filter (·.1 == k)).length
  { s with
    n := s.n + 1
    outOfRange := s.outOfRange + (if o.out then 1 else 0)
    literalFalse := s.literalFalse + (if o.literalFalse then 1 else 0)
    unsound := s.unsound + count "unsound"
    loose := s.loose + count "loose"
    range := s.range + count "range"
    value := s.value + count "value"
    first := match s.first, o.fails with
      | none, (k, msg) :: _ => some s!"[{k}] {msg}"
      | f, _ => f }

/-- The number of failures in a tally: unsound, loose, range and value. -/
def Stat.failures (s : Stat) : Nat := s.unsound + s.loose + s.range + s.value

/-- A directed operation at `a` `b` against the model: `lo`, `hi` are the soft-float's round-down
and round-up of the exact `x`, and NaN is expected exactly where `stepBits` says. -/
def checkDirected (name : String) (up : Bool) (native : Float) (a b : Float) (x : Rat)
    (lo hi : IEEE IEEEFormat.binary64) (xZero : Bool) : Outcome :=
  let soft := if up then hi else lo
  let exp := stepBits (rnOf x lo hi) up xZero
  let line := s!"{name} a={aux_hexF a} b={aux_hexF b} native={aux_hexF native} " ++
    s!"soft={aux_soft soft} expected={aux_expect exp}"
  let qn := qOf native
  match exp with
  | none =>
    -- the model says NaN; the axiom as stated (up only) holds of a NaN's decoded value or not
    let lit := up && !(x ≤ qn)
    if aux_nan native then { out := true, literalFalse := lit }
    else { out := true, literalFalse := lit, fails := [("range", "expected NaN: " ++ line)] }
  | some _ =>
    if aux_nan native || !native.isFinite then
      { fails := [("range", "expected a number: " ++ line)] }
    else
      let qs := qIEEE soft
      let qt := qStep soft up
      let fs : List Fail :=
        if up then
          (if qs ≤ qn then [] else [("unsound", "below the exact bound: " ++ line)]) ++
          (if qn ≤ qt then [] else [("loose", "beyond one step: " ++ line)])
        else
          (if qn ≤ qs then [] else [("unsound", "above the exact bound: " ++ line)]) ++
          (if qt ≤ qn then [] else [("loose", "beyond one step: " ++ line)])
      { fails := fs }

/-- `half`: exactly `a / 2` where that is zero or normal, NaN otherwise. -/
def checkHalf (a : Float) : Outcome :=
  let h := Binary64.half a
  let qa := qOf a
  let line := s!"half a={aux_hexF a} native={aux_hexF h}"
  let minNormal : Rat := dq 1 (-1022)
  let inR := a.isFinite && (qa == 0 || minNormal ≤ (if qa < 0 then -qa else qa) / 2)
  if inR then
    if aux_nan h || qOf h != qa / 2 then { fails := [("value", "not a / 2: " ++ line)] } else {}
  else if aux_nan h then { out := true, literalFalse := a.isFinite && qOf h != qa / 2 }
  else { out := true, fails := [("range", "expected NaN: " ++ line)] }

/-- `neg`: the sign bit flipped and nothing else. A NaN is the exception: Lean's `toBits` reports
every NaN as `0x7FF8000000000000`, so `toReal (-a) = -toReal a` is false of one as stated, and only
a NaN result is required there. -/
def checkNeg (a : Float) : Outcome :=
  let n := -a
  let line := s!"neg a={aux_hexF a} native={aux_hexF n}"
  if a.isNaN then
    if aux_nan n then { out := true, literalFalse := qOf n != -qOf a }
    else { out := true, fails := [("value", "expected NaN: " ++ line)] }
  else if n.toBits != a.toBits ^^^ 0x8000000000000000 then
    { fails := [("value", "sign bit: " ++ line)] }
  else if qOf n != -qOf a then { fails := [("value", "toReal: " ++ line)] }
  else {}

/-- `minimum` and `maximum`: the decoded lesser (greater) of the two; NaN if either is NaN. -/
def checkMinMax (isMin : Bool) (a b : Float) : Outcome :=
  let r := if isMin then Binary64.minimum a b else Binary64.maximum a b
  let name := if isMin then "minimum" else "maximum"
  let line := s!"{name} a={aux_hexF a} b={aux_hexF b} native={aux_hexF r}"
  if a.isNaN || b.isNaN then
    if aux_nan r then {} else { fails := [("value", "expected NaN: " ++ line)] }
  else
    let qa := qOf a
    let qb := qOf b
    let e := if isMin then min qa qb else max qa qb
    if !aux_nan r && qOf r == e then {} else { fails := [("value", "not the exact one: " ++ line)] }

/-- `≤`: the implication the axiom states, and its converse, on non-NaN inputs; false on a NaN. -/
def checkLe (a b : Float) : Outcome :=
  let r := decide (a ≤ b)
  let line := s!"le a={aux_hexF a} b={aux_hexF b} native={r}"
  if a.isNaN || b.isNaN then
    if r then { fails := [("value", "a NaN compared ≤: " ++ line)] } else {}
  else
    let d := qOf a ≤ qOf b
    if r && !d then { fails := [("unsound", "≤ but decoded greater: " ++ line)] }
    else if !r && d then { fails := [("loose", "not ≤ but decoded ≤: " ++ line)] }
    else {}

/-- The two literals decode to `0` and `1`. -/
def checkLiterals (zero one : Float) : Outcome :=
  { fails :=
      (if qOf zero == 0 then [] else [("value", s!"0.0 decodes to {qOf zero}")]) ++
      (if qOf one == 1 then [] else [("value", s!"1.0 decodes to {qOf one}")]) }

/-- A non-finite input must give NaN from every rounded operation, but `0 / +∞`, which is `0`. -/
def checkNonFinite (name : String) (native : Float) (a b : Float) (zeroOk : Bool) : Outcome :=
  let line := s!"{name} a={aux_hexF a} b={aux_hexF b} native={aux_hexF native}"
  if zeroOk then
    if !aux_nan native && qOf native == 0 then {}
    else { fails := [("range", "expected 0: " ++ line)] }
  else if aux_nan native then { out := true }
  else { out := true, fails := [("range", "expected NaN: " ++ line)] }

end CORALean.HardwareCheck


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
