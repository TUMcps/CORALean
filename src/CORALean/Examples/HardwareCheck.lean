import CORALean.Examples.HardwareCheck.Checks
import CORALean.Global.Float.Instances.Binary64.Operations.Basic
import CORALean.Global.Float.Instances.Binary64.Operations.DivDown
import CORALean.Global.Float.Instances.IEEE.Operations.Basic
import CORALean.Global.Float.Instances.IEEE.Operations.AddUp
import CORALean.Global.Float.Instances.IEEE.Operations.DivUp
import CORALean.Global.Float.Instances.IEEE.Operations.MulUp

/-!
# `lake exe hardwarecheck`: does the machine do what `IsTrustedHardware` says?

`IsTrustedHardware` is false as stated (`not_isTrustedHardware`); its field docstrings claim
instead that each conjunct holds wherever its result is a number. This executable SAMPLES that, at
every input, NaN, `±∞`, subnormals and overflow included (the `number` column), and compares every
native result exactly with the axiom-free soft-float `IEEE .binary64` on random and structured bit
patterns (`Rng.lean`); the operations must return NaN exactly outside the normal range (`stepUp`,
`step_inRange`). Build it linked (`lake build hardwarecheck`) so that it tests the C lake emits;
`lake exe hardwarecheck [--seed N] [--n N]` exits `1` on any violation, `0` otherwise.

## Inputs
* `args` – command line arguments

## Output
* exit code zero when no sample violates the claims
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   10-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open CORALean.HardwareCheck CORALean.Float CORALean.Bench

/-- The operations, in report order. -/
def opNames : Array String :=
  #["addUp", "addDown", "mulUp", "mulDown", "divUp", "divDown", "half", "neg", "minimum",
    "maximum", "le", "literals", "nonfinite-in"]

def freshTally : Array Stat := opNames.map fun n => { name := n }

def record (t : Array Stat) (name : String) (o : Outcome) : Array Stat :=
  match opNames.findIdx? (· == name) with
  | some i => t.modify i (·.add o)
  | none => t

/-- `record`, with the conjunct of the operation `op` checked at its result `r` (`withField`). -/
def recordAt (t : Array Stat) (name op : String) (a b r : Float) (o : Outcome) : Array Stat :=
  record t name (withField op a b r o)

/-- The sums, products and quotients of one pair, in both directions. -/
def runArith (t : Array Stat) (a b : Float) : Array Stat :=
  let fa := floatToIEEE64 a
  let fb := floatToIEEE64 b
  let qa := qOf a
  let qb := qOf b
  let dir (t : Array Stat) (name : String) (up : Bool) (r : Float) (x : Rat) (lo hi : IEEE _) :=
    recordAt t name name a b r (checkDirected name up r a b x lo hi (x == 0))
  let t := dir t "addUp" true (Binary64.addUp a b) (qa + qb) (IEEE.addDown fa fb) (IEEE.addUp fa fb)
  let t := dir t "addDown" false (Binary64.addDown a b) (qa + qb) (IEEE.addDown fa fb)
    (IEEE.addUp fa fb)
  let t := dir t "mulUp" true (Binary64.mulUp a b) (qa * qb) (IEEE.mulDown fa fb) (IEEE.mulUp fa fb)
  dir t "mulDown" false (Binary64.mulDown a b) (qa * qb) (IEEE.mulDown fa fb) (IEEE.mulUp fa fb)

/-- The quotients of `a` by `b`, positive and nonzero. -/
def runDiv (t : Array Stat) (a b : Float) : Array Stat :=
  let fa := floatToIEEE64 a
  let fb := floatToIEEE64 b
  let x := qOf a / qOf b
  let t := recordAt t "divUp" "divUp" a b (Binary64.divUp a b) (checkDirected "divUp" true
    (Binary64.divUp a b) a b x (IEEE.divDown fa fb) (IEEE.divUp fa fb) (x == 0))
  recordAt t "divDown" "divDown" a b (Binary64.divDown a b) (checkDirected "divDown" false
    (Binary64.divDown a b) a b x (IEEE.divDown fa fb) (IEEE.divUp fa fb) (x == 0))

/-- The exact operations on one pair: `half`, `neg`, `minimum`, `maximum` and `≤`. -/
def runExact (t : Array Stat) (a b : Float) : Array Stat :=
  let t := recordAt t "half" "half" a a (Binary64.half a) (checkHalf a)
  let t := recordAt t "neg" "neg" a a (-a) (checkNeg a)
  let t := recordAt t "minimum" "minimum" a b (Binary64.minimum a b) (checkMinMax true a b)
  let t := recordAt t "maximum" "maximum" a b (Binary64.maximum a b) (checkMinMax false a b)
  record t "le" (checkLe a b)

/-- Every operation on one pair of finite bit patterns. -/
def runFinite (t : Array Stat) (ab bb : UInt64) : Array Stat :=
  let a := Float.ofBits ab
  let b := Float.ofBits bb
  let t := recordAt t "half" "half" b b (Binary64.half b) (checkHalf b)
  let t := runExact t a b
  let t := runArith t a b
  -- a divisor is positive: the axiom asks no more, so `b` loses its sign, and a zero is skipped
  let bp := Float.ofBits (bb &&& 0x7FFFFFFFFFFFFFFF)
  if bp.toBits == 0 then t else runDiv t a bp

/-- The non-finite inputs against every operation. -/
def runNonFinite (t : Array Stat) : Array Stat := Id.run do
  let mut t := t
  let others := nonFinite ++ finiteProbe
  for ab in nonFinite do
    for ob in others do
      for (xb, yb) in [(ab, ob), (ob, ab)] do
        let a := Float.ofBits xb
        let b := Float.ofBits yb
        t := runExact t a b
        for (op, r) in [("addUp", Binary64.addUp a b), ("addDown", Binary64.addDown a b),
            ("mulUp", Binary64.mulUp a b), ("mulDown", Binary64.mulDown a b)] do
          t := recordAt t "nonfinite-in" op a b r (checkNonFinite op r a b false)
        let bp := Float.ofBits (yb &&& 0x7FFFFFFFFFFFFFFF)
        if bp.toBits != 0 then
          -- `0 / +∞` is the one exact zero
          let z := (xb <<< 1 == 0) && bp.toBits == 0x7FF0000000000000
          for (op, r) in [("divUp", Binary64.divUp a bp), ("divDown", Binary64.divDown a bp)] do
            t := recordAt t "nonfinite-in" op a bp r (checkNonFinite op r a bp z)
  pure t

def defaultSeed : Nat := 20260930
def defaultN : Nat := 100000

def parseArgs : List String → Nat × Nat → Except String (Nat × Nat)
  | [], r => pure r
  | "--seed" :: v :: rest, (_, n) => match v.toNat? with
    | some s => parseArgs rest (s, n)
    | none => throw s!"--seed wants a natural number, got `{v}`"
  | "--n" :: v :: rest, (s, _) => match v.toNat? with
    | some n => parseArgs rest (s, n)
    | none => throw s!"--n wants a natural number, got `{v}`"
  | a :: _, _ => throw s!"unknown argument `{a}`; usage: hardwarecheck [--seed N] [--n N]"

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

def report (t : Array Stat) : IO Unit := do
  -- the table, one row per operation, then the first failing input of each
  IO.println (pad "op" 14 ++ pad "samples" 9 ++ pad "outOfRange" 11 ++ pad "litFalse" 9 ++
    pad "unsound" 8 ++ pad "loose" 7 ++ pad "range" 7 ++ pad "value" 7 ++ "number")
  for s in t do
    IO.println (pad s.name 14 ++ pad (toString s.n) 9 ++ pad (toString s.outOfRange) 11 ++
      pad (toString s.literalFalse) 9 ++ pad (toString s.unsound) 8 ++ pad (toString s.loose) 7 ++
      pad (toString s.range) 7 ++ pad (toString s.value) 7 ++ toString s.number)
  IO.println "outOfRange: the model puts the result outside the normal range (NaN required)"
  IO.println "litFalse:   the conjunct as stated is false, on the decoded values"
  IO.println "number:     ... of a result that is a number, not a NaN (must be 0)"
  for s in t do
    if let some f := s.first then IO.println s!"FIRST FAILURE {f}"


-- =====================================  MAIN DEFINITION  ====================================== --

def main (args : List String) : IO UInt32 := do
  match parseArgs args (defaultSeed, defaultN) with
  | .error e => IO.eprintln e; pure 2
  | .ok (seed, n) =>
    IO.println s!"hardwarecheck seed={seed} n={n} (random pairs; structured pairs in addition)"
    let mut t := freshTally
    -- the literals and every pair of specials, then the non-finite inputs, then `n` random pairs
    t := record t "literals" (checkLiterals 0.0 1.0)
    for a in specials do
      for b in specials do
        t := runFinite t a b
    t := runNonFinite t
    let mut g : Rng := ⟨seed.toUInt64⟩
    for i in [0:n] do
      let (p, g') := pairOf i g
      g := g'
      if isFin p.1 && isFin p.2 then t := runFinite t p.1 p.2
    report t
    let bad := t.foldl (fun acc s => acc + s.failures) 0
    if bad == 0 then
      IO.println "OK: no violation"
      pure 0
    else
      IO.println s!"FAIL: {bad} violation(s)"
      pure 1


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
