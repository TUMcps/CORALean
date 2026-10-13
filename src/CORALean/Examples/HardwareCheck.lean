import CORALean.Examples.HardwareCheck.Checks

/-!
# `lake exe hardwarecheck`: does the machine do what `TrustedHardware` says?

`Float` is opaque in Lean's logic, so the ten conjuncts of `TrustedHardware` are trusted claims
about the machine and about the C the compiler emitted for `Binary64`'s operations; nothing proves
them. This executable SAMPLES them, and is only as strong as its sampling: every native result is
compared, exactly, with the axiom-free soft-float `IEEE .binary64`, on uniform random bit patterns
and on structured inputs (`Rng.lean`), and the operations must return NaN exactly outside the normal
range (`Binary64/Operations/InRange.lean`). `Exact.lean` and `Checks.lean` define the comparison.

Build it linked -- `lake build hardwarecheck` -- so that it tests the C lake emits, not the
toolchain's precompiled primitives, which `lake env lean --run` would test instead.

    lake exe hardwarecheck [--seed N] [--n N]

Prints the seed, the samples per operation and the first failing input of each; exits `1` on any
violation, `0` otherwise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
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

/-- The sums, products and quotients of one pair, in both directions. -/
def runArith (t : Array Stat) (a b : Float) : Array Stat :=
  let fa := floatToIEEE64 a
  let fb := floatToIEEE64 b
  let qa := qOf a
  let qb := qOf b
  let dir (t : Array Stat) (name : String) (up : Bool) (r : Float) (x : Rat) (lo hi : IEEE _) :=
    record t name (checkDirected name up r a b x lo hi (x == 0))
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
  let t := record t "divUp" (checkDirected "divUp" true (Binary64.divUp a b) a b x
    (IEEE.divDown fa fb) (IEEE.divUp fa fb) (x == 0))
  record t "divDown" (checkDirected "divDown" false (Binary64.divDown a b) a b x
    (IEEE.divDown fa fb) (IEEE.divUp fa fb) (x == 0))

/-- Every operation on one pair of finite bit patterns. -/
def runFinite (t : Array Stat) (ab bb : UInt64) : Array Stat :=
  let a := Float.ofBits ab
  let b := Float.ofBits bb
  let t := record t "half" (checkHalf a)
  let t := record t "half" (checkHalf b)
  let t := record t "neg" (checkNeg a)
  let t := record t "minimum" (checkMinMax true a b)
  let t := record t "maximum" (checkMinMax false a b)
  let t := record t "le" (checkLe a b)
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
        t := record t "half" (checkHalf a)
        t := record t "neg" (checkNeg a)
        t := record t "minimum" (checkMinMax true a b)
        t := record t "maximum" (checkMinMax false a b)
        t := record t "le" (checkLe a b)
        t := record t "nonfinite-in" (checkNonFinite "addUp" (Binary64.addUp a b) a b false)
        t := record t "nonfinite-in" (checkNonFinite "addDown" (Binary64.addDown a b) a b false)
        t := record t "nonfinite-in" (checkNonFinite "mulUp" (Binary64.mulUp a b) a b false)
        t := record t "nonfinite-in" (checkNonFinite "mulDown" (Binary64.mulDown a b) a b false)
        let bp := Float.ofBits (yb &&& 0x7FFFFFFFFFFFFFFF)
        if bp.toBits != 0 then
          -- `0 / +∞` is the one exact zero
          let z := (xb <<< 1 == 0) && bp.toBits == 0x7FF0000000000000
          t := record t "nonfinite-in" (checkNonFinite "divUp" (Binary64.divUp a bp) a bp z)
          t := record t "nonfinite-in" (checkNonFinite "divDown" (Binary64.divDown a bp) a bp z)
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
    pad "unsound" 8 ++ pad "loose" 7 ++ pad "range" 7 ++ "value")
  for s in t do
    IO.println (pad s.name 14 ++ pad (toString s.n) 9 ++ pad (toString s.outOfRange) 11 ++
      pad (toString s.literalFalse) 9 ++ pad (toString s.unsound) 8 ++ pad (toString s.loose) 7 ++
      pad (toString s.range) 7 ++ toString s.value)
  IO.println "outOfRange: the model puts the result outside the normal range (NaN required)"
  IO.println "litFalse:   of those, the axiom's inequality, on the NaN's decoding, is false"
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
