import CORALean.Examples.Bench.OpCompareCodec

/-!
# Exact decoding and the round-to-nearest model

Everything `hardwarecheck` compares is an exact rational: `qOf` decodes a `Float` as `toReal` does
(`Binary64.toDyadic`, NaN and `∞` included, where it denotes no number), and `qIEEE` reads a
soft-float `IEEE .binary64` result. `rnOf` is IEEE 754's round-to-nearest-even of an exact value,
read off the soft-float's own round-down and round-up. `stepBits` is `stepUp`'s specification, "one
step out from the nearest float, NaN out of range", written on bit patterns independently of it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.HardwareCheck

open CORALean.Float CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `m * 2 ^ e`, exactly. -/
def dq (m e : Int) : Rat :=
  if 0 ≤ e then Rat.ofInt (m * 2 ^ e.toNat) else Rat.ofInt m / Rat.ofInt (2 ^ (-e).toNat)

/-- What `Binary64.toReal x` denotes, exactly; for a NaN or `∞` the number `toReal` assigns them. -/
def qOf (x : Float) : Rat :=
  let d := Binary64.toDyadic x
  dq d.mantissa d.exponent

/-- A soft-float result's exact value. -/
def qIEEE (x : IEEE IEEEFormat.binary64) : Rat := dq x.mantissa x.exponent

/-- The soft result with a mantissa of at most 53 bits: a round-up that carries into the next power
of two leaves `2 ^ 53`, which `ieee64ToBits` refuses. -/
def normIEEE (x : IEEE IEEEFormat.binary64) : IEEE IEEEFormat.binary64 :=
  if 53 < x.mantissa.natAbs.log2 + 1 then ⟨x.mantissa / 2, x.exponent + 1⟩ else x

/-- The bit pattern of a soft result, `none` past the format's finite range. -/
def bitsOf (x : IEEE IEEEFormat.binary64) : Option UInt64 :=
  (ieee64ToBits (normIEEE x)).toOption

/-- The nearest binary64 to an exact value, on the format's grid but with an unbounded exponent. -/
inductive Rn where
  | fin (bits : UInt64)
  | inf

def Rn.ofSoft (x : IEEE IEEEFormat.binary64) : Rn :=
  match bitsOf x with
  | some b => .fin b
  | none => .inf

/-- Round-to-nearest, ties to even, of the exact `x`, whose neighbours on the grid are `lo ≤ x ≤ hi`
(the soft-float's round-down and round-up of it). -/
def rnOf (x : Rat) (lo hi : IEEE IEEEFormat.binary64) : Rn :=
  let l := qIEEE lo
  let h := qIEEE hi
  if l == h then Rn.ofSoft lo
  else if x - l < h - x then Rn.ofSoft lo
  else if h - x < x - l then Rn.ofSoft hi
  else
    match bitsOf lo with
    | some b => if b &&& 1 == 0 then .fin b else Rn.ofSoft hi
    | none => .inf

/-- The bit pattern one step above (`up`) or below the finite, nonzero `b`. -/
def stepRaw (b : UInt64) (up : Bool) : UInt64 :=
  if (b >>> 63 == 0) == up then b + 1 else b - 1

/-- What a directed operation must return given the nearest result `r` of the exact `x`: `none`
for NaN, else the exact bit pattern. A zero stays only where the exact result is zero
(`xZero`); a subnormal, `∞` or a step out of the normal range is NaN. -/
def stepBits (r : Rn) (up xZero : Bool) : Option UInt64 :=
  match r with
  | .inf => none
  | .fin b =>
    let e := (b >>> 52) &&& 0x7FF
    if e == 0 then (if b <<< 1 == 0 && xZero then some b else none)
    else
      let s := stepRaw b up
      let e' := (s >>> 52) &&& 0x7FF
      if e' == 0 || e' == 0x7FF then none else some s

/-- The value of the float one step out from the soft result `s`, or `s` itself where none is
to be named (a zero, or past the range). -/
def qStep (s : IEEE IEEEFormat.binary64) (up : Bool) : Rat :=
  match bitsOf s with
  | some b => if b <<< 1 == 0 then qIEEE s else qOf (Float.ofBits (stepRaw b up))
  | none => qIEEE s

end CORALean.HardwareCheck


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
