import CORALean.Global.Float.Instances.Flint.API

/-!
# `lake exe flintcheck`: does FLINT do what `trustedFlint` says?

`trustedFlint` (`Flint/Definitions/Axioms.lean`) is a claim about C no proof reaches; this SAMPLES
it, as `hardwarecheck` does `IsTrustedHardware`, against exact rationals with the rounding written
out from the definition. For each directed operation, precision `p` and operand pair (bit lengths
about `p`, ties, cancellation, zeros, a positive divisor), with `x` the exact result, `r` must lie
on the claimed side of `x`, have at most `p` significant bits, and be the nearest such number. Run
`lake exe flintcheck [--seed N] [--n N]` after `scripts/install-flint.sh` and
`scripts/build-flint-shim.sh`; it exits `1` on any violation (CI job `flint-check`).

## Inputs
* `t` – statistics so far
* `p` – significand width
* `n` – number of samples
* `seed` – random seed

## Output
* statistics updated by the samples at that width
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open CORALean.Float

namespace CORALean.FlintCheck


/-- Tally of one operation. -/
structure Stat where
  name : String
  n : Nat := 0
  wrongDirection : Nat := 0
  notRepresentable : Nat := 0
  notTightest : Nat := 0
  first : Option String := none

def Stat.failures (s : Stat) : Nat := s.wrongDirection + s.notRepresentable + s.notTightest


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- SplitMix64, so a seed reproduces a run everywhere. -/
def aux_next (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z := (s' ^^^ (s' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s')

/-- Uniform in `[0, k)`, up to a modulo bias no test here can see. -/
def aux_below (s : UInt64) (k : Nat) : Nat × UInt64 :=
  let (u, s) := aux_next s
  (u.toNat % k, s)

/-- `m * 2 ^ e` as an exact rational. -/
def aux_dq (m e : Int) : Rat :=
  if 0 ≤ e then Rat.ofInt (m * 2 ^ e.toNat) else Rat.ofInt m / Rat.ofInt (2 ^ (-e).toNat)

/-- `2 ^ k` as an exact rational. -/
def aux_pow2 (k : Int) : Rat := aux_dq 1 k

def aux_value {p : ℕ} (a : Flint p) : Rat := aux_dq a.mantissa a.exponent

/-- `⌊log₂ |x|⌋` for `x ≠ 0`. -/
def aux_log2 (x : Rat) : Int :=
  let k : Int := (x.num.natAbs.log2 : Int) - (x.den.log2 : Int)
  if |x| < aux_pow2 k then k - 1 else k

/-- The model: the least (`up`) or greatest number with at most `p` significant bits on the
right side of `x`: in the binade of `|x|`, a multiple of `2 ^ (⌊log₂ |x|⌋ - p + 1)`. -/
def aux_round (up : Bool) (p : ℕ) (x : Rat) : Rat :=
  if x == 0 then 0 else
  let u := aux_log2 x - (p : Int) + 1
  let q := x / aux_pow2 u
  Rat.ofInt (if up then q.ceil else q.floor) * aux_pow2 u

/-- Significant bits of `m * 2 ^ e`: the bit length of `m` with trailing zeros dropped. -/
def aux_sigBits (m : Int) : Nat :=
  if m == 0 then 0 else
  let a := m.natAbs
  let rec strip (a : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => a
    | f + 1 => if a % 2 == 0 then strip (a / 2) f else a
  (strip a (a.log2 + 1)).log2 + 1

/-- `m * 2 ^ e` reduced to an odd mantissa (zero as `(0, 0)`), for comparing representations. -/
def aux_norm (m e : Int) : Int × Int :=
  if m == 0 then (0, 0) else
  let rec go (a : Nat) (e : Int) (fuel : Nat) : Nat × Int :=
    match fuel with
    | 0 => (a, e)
    | f + 1 => if a % 2 == 0 then go (a / 2) (e + 1) f else (a, e)
  let (a, e') := go m.natAbs e (m.natAbs.log2 + 1)
  (if m < 0 then -(a : Int) else (a : Int), e')

def Stat.add (t : Stat) (desc : String) (dir ok repr tight : Bool) : Stat :=
  let t := { t with n := t.n + 1 }
  if dir && ok && repr && tight then t else
  { t with
    wrongDirection := t.wrongDirection + (if ok then 0 else 1)
    notRepresentable := t.notRepresentable + (if repr then 0 else 1)
    notTightest := t.notTightest + (if tight then 0 else 1)
    first := t.first.orElse fun _ => some desc }

/-- One directed result `r` of `op` at `p`, with exact value `x`, against all three properties. -/
def aux_check (t : Stat) (up : Bool) (p : ℕ) (a b r : Flint p) (x : Rat) : Stat :=
  let v := aux_value r
  let ok := if up then x ≤ v else v ≤ x
  let repr := aux_sigBits r.mantissa ≤ max p 2
  let tight := v == aux_round up (max p 2) x
  t.add s!"p={p} a=({a.mantissa},{a.exponent}) b=({b.mantissa},{b.exponent}) \
    result=({r.mantissa},{r.exponent}) exact={x}" true ok repr tight


/-- A random natural of the given bit length (top bit set), zero for length `0`. -/
def aux_bits (s : UInt64) (len : Nat) : Nat × UInt64 := Id.run do
  if len == 0 then return (0, s)
  let mut s := s
  let mut acc : Nat := 0
  for _ in [0:(len + 63) / 64] do
    let (u, s') := aux_next s
    s := s'
    acc := acc * 2 ^ 64 + u.toNat
  (acc % 2 ^ len ||| 2 ^ (len - 1), s)

/-- A mantissa for precision `p`: random, near `p` or `p + 1` bits, `2^k ± 1`, a power of two, or a
tie (`p + 1` bits, the last set), signed by a further bit. -/
def aux_mantissa (s : UInt64) (p : Nat) : Int × UInt64 :=
  let (cls, s) := aux_below s 8
  let (r, s) := aux_below s (p + 70)
  let (sg, s) := aux_below s 2
  let (m, s) : Nat × UInt64 :=
    match cls with
    | 0 => aux_bits s (r % 4)
    | 1 => aux_bits s (p + 1)
    | 2 => aux_bits s (p + r % 3)
    | 3 => ((2 ^ (r % (p + 66)) : Nat) + 1, s)
    | 4 => ((2 ^ (r % (p + 66)) : Nat) - 1, s)
    | 5 => (2 ^ (r % (p + 66)), s)
    | 6 => let (u, s) := aux_bits s p; (u * 2 + 1, s)
    | _ => aux_bits s (r + 1)
  (if sg == 0 then -(m : Int) else (m : Int), s)

/-- An exponent: close to the origin, or far from it (the gap between operands decides whether an
addend is a sticky bit only). -/
def aux_exponent (s : UInt64) : Int × UInt64 :=
  let (c, s) := aux_below s 4
  let (r, s) := aux_below s 1000
  (if c == 0 then (r : Int) - 500 else (r % 41 : Nat) - 20, s)

def precisions : List Nat := [2, 3, 8, 11, 24, 53, 64, 113, 200]

def opNames : Array String :=
  #["addUp", "addDown", "mulUp", "mulDown", "divUp", "divDown", "conversion"]

def freshTally : Array Stat := opNames.map fun n => { name := n }

def record (t : Array Stat) (name : String) (f : Stat → Stat) : Array Stat :=
  match opNames.findIdx? (· == name) with
  | some i => t.modify i f
  | none => t

/-- The six operations at one pair of operands. -/
def runPair (t : Array Stat) (p : ℕ) (a b : Flint p) : Array Stat :=
  let va := aux_value a
  let vb := aux_value b
  let t := record t "addUp" (aux_check · true p a b (Flint.addUp p a b) (va + vb))
  let t := record t "addDown" (aux_check · false p a b (Flint.addDown p a b) (va + vb))
  let t := record t "mulUp" (aux_check · true p a b (Flint.mulUp p a b) (va * vb))
  let t := record t "mulDown" (aux_check · false p a b (Flint.mulDown p a b) (va * vb))
  -- a divisor is positive: the axiom asks no more
  if vb == 0 then t else
  let b' : Flint p := ⟨b.mantissa.natAbs, b.exponent⟩
  let q := va / aux_value b'
  let t := record t "divUp" (aux_check · true p a b' (Flint.divUp p a b') q)
  record t "divDown" (aux_check · false p a b' (Flint.divDown p a b') q)

/-- The shim's `Int`/`fmpz` conversion: `a + 0` and `a * 1` are `a`, at a precision that rounds
nothing, in both directions. Compared by odd mantissa and exponent, so that exponents past `2^64`
need no rational. -/
def runConversion (t : Array Stat) (m e : Int) : Array Stat :=
  let p := max (aux_sigBits m) 2 + 1
  let a : Flint p := ⟨m, e⟩
  let zero : Flint p := ⟨0, 0⟩
  let one : Flint p := ⟨1, 0⟩
  let want := aux_norm m e
  let chk (name : String) (r : Flint p) (t : Stat) :=
    let ok := aux_norm r.mantissa r.exponent == want
    t.add s!"{name} a=({m},{e}) result=({r.mantissa},{r.exponent})" true true true ok
  record t "conversion" fun s =>
    chk "addUp" (Flint.addUp p a zero) <| chk "addDown" (Flint.addDown p a zero) <|
    chk "mulUp" (Flint.mulUp p a one) <| chk "mulDown" (Flint.mulDown p a one) s


def defaultSeed : Nat := 20261008
def defaultN : Nat := 3000

def parseArgs : List String → Nat × Nat → Except String (Nat × Nat)
  | [], r => pure r
  | "--seed" :: v :: rest, (_, n) => match v.toNat? with
    | some s => parseArgs rest (s, n)
    | none => throw s!"--seed wants a natural number, got `{v}`"
  | "--n" :: v :: rest, (s, _) => match v.toNat? with
    | some n => parseArgs rest (s, n)
    | none => throw s!"--n wants a natural number, got `{v}`"
  | a :: _, _ => throw s!"unknown argument `{a}`; usage: flintcheck [--seed N] [--n N]"

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

def report (t : Array Stat) : IO Unit := do
  IO.println (pad "op" 12 ++ pad "samples" 9 ++ pad "direction" 11 ++ pad "repres." 9 ++ "tightest")
  for s in t do
    IO.println (pad s.name 12 ++ pad (toString s.n) 9 ++ pad (toString s.wrongDirection) 11 ++
      pad (toString s.notRepresentable) 9 ++ toString s.notTightest)
  IO.println "direction / repres. / tightest: failures of each property (0 expected)"
  for s in t do
    if let some f := s.first then IO.println s!"FIRST FAILURE {s.name}: {f}"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One round of `n` operand pairs at precision `p`, in the order of the generators. -/
def runPrecision (t : Array Stat) (p : ℕ) (n : Nat) (seed : UInt64) : Array Stat := Id.run do
  let mut t := t
  let mut s := seed + p.toUInt64
  for i in [0:n] do
    let (m1, s1) := aux_mantissa s p
    let (e1, s2) := aux_exponent s1
    let (m2, s3) := aux_mantissa s2 p
    let (e2, s4) := aux_exponent s3
    s := s4
    let a : Flint p := ⟨m1, e1⟩
    -- every eighth pair cancels exactly or leaves only the low bits
    let b : Flint p :=
      if i % 8 == 0 then ⟨-m1, e1⟩ else
      if i % 8 == 1 then ⟨-m1 + 1, e1⟩ else ⟨m2, e2⟩
    t := runPair t p a b
  pure t

/-- The `flintcheck` executable: samples the directed operations of FLINT per precision against
exact rationals, prints a tally, and exits `0` without a violation, `1` with one, `2` on bad
arguments. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args (defaultSeed, defaultN) with
  | .error e => IO.eprintln e; pure 2
  | .ok (seed, n) =>
    IO.println s!"flintcheck seed={seed} n={n} per precision, precisions {precisions}"
    let mut t := freshTally
    for p in precisions do
      -- `p` is data to FLINT but a type index to `Flint p`: one instantiation per precision
      t := runPrecision t p n seed.toUInt64
    let mut s : UInt64 := seed.toUInt64
    for _ in [0:n] do
      let (m, s1) := aux_mantissa s 200
      let (r, s2) := aux_below s1 4
      let (e, s3) := aux_exponent s2
      s := s3
      -- exponents past `2^64`, positive and negative, beside the small ones
      let e' : Int := if r == 0 then (2 : Int) ^ 70 + e else if r == 1 then -(2 : Int) ^ 70 + e
        else e
      t := runConversion t m e'
    report t
    let bad := t.foldl (fun acc s => acc + s.failures) 0
    if bad == 0 then
      IO.println "OK: no violation"
      pure 0
    else
      IO.println s!"FAIL: {bad} violation(s)"
      pure 1

end CORALean.FlintCheck

/-- The entry point of the executable. -/
def main := CORALean.FlintCheck.main


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
