import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.IEEE.API

/-!
# `opcompare`: hex bit patterns, and the exact `Float ↔ IEEE .binary64` conversion

`inputs.json`/`matlab_results.json` (`experiments/matlab-ops/make_inputs.py`) hold every
number as 16 lowercase hex digits, most significant first -- `struct.pack('>d', x).hex()`,
with no `0x` prefix -- and this bench's own `coralean_results.json` matches that convention
exactly, so `compare.py` reads every field, from either side, the same way.

`ieee64ToBits` is the interesting half: `floatToIEEE64` carries a `Float` into `IEEE
.binary64` losslessly (`Binary64.toDyadic`'s own `(mantissa, exponent)`), but the rounded
operations (`addDown`, `mulUp`, ...) leave the pair in whatever un-normalised form the grid
arithmetic produced, and turning that back into a bit pattern means finding the *standard*
binary64 form -- normal or subnormal -- that denotes the same value. `checkRoundTrip` is the
regression: every input hex token survives `hex → Float → IEEE → hex` unchanged.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One hex digit's value, upper or lower case. -/
def aux_hexVal (c : Char) : Except String UInt64 :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat.toUInt64 - '0'.toNat.toUInt64)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat.toUInt64 - 'a'.toNat.toUInt64 + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat.toUInt64 - 'A'.toNat.toUInt64 + 10)
  else throw s!"`{c}` is not a hex digit"

/-- The inverse: a nibble `0`..`15` as a lowercase hex digit. -/
def aux_hexChar (v : UInt64) : Char :=
  if v < 10 then Char.ofNat (v + '0'.toNat.toUInt64).toNat
  else Char.ofNat (v - 10 + 'a'.toNat.toUInt64).toNat


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A 16-hex-digit token as the `UInt64` it spells, most significant digit first --
`make_inputs.py`'s own bit pattern, read back. -/
def parseHex64 (s : String) : Except String UInt64 := do
  if s.length ≠ 16 then throw s!"`{s}` is not a 16-hex-digit binary64 bit pattern" else
  let digits ← s.toList.mapM aux_hexVal
  pure (digits.foldl (fun acc d => acc * 16 + d) 0)

/-- The inverse: 16 lowercase hex digits, most significant first -- the one convention every
hex field, in or out, uses. -/
def uint64ToHex (u : UInt64) : String :=
  String.ofList ((List.range 16).map fun i => aux_hexChar ((u >>> (60 - 4 * i).toUInt64) &&& 0xF))

def hexToFloat (s : String) : Except String Float := (parseHex64 s).map Float.ofBits

def floatToHex (x : Float) : String := uint64ToHex x.toBits

/-- `x` at `IEEE .binary64`, exactly -- `Binary64.toDyadic`'s own `(mantissa, exponent)`,
which is what `IEEE`'s representation stores, so no rounding happens on the way in. -/
def floatToIEEE64 (x : Float) : IEEE IEEEFormat.binary64 :=
  let d := Binary64.toDyadic x
  ⟨d.mantissa, d.exponent⟩

/-- `x`'s exact binary64 bit pattern -- see the module docstring for how. Fails only past the
format's finite range or off the grid entirely, neither of which a rounded result can be. -/
def ieee64ToBits (x : IEEE IEEEFormat.binary64) : Except String UInt64 :=
  if IEEE.overflows x then
    throw s!"{x.mantissa}*2^{x.exponent} exceeds binary64's largest finite value"
  else if x.mantissa = 0 then pure 0
  else
    let sign : UInt64 := if x.mantissa < 0 then 1 else 0
    let m := x.mantissa.natAbs
    -- `len`: how many bits `m` needs; `lead`: the exponent of its leading (most significant) bit
    let len := m.log2 + 1
    let lead : Int := x.exponent + (len : Int) - 1
    if len > 53 then throw s!"{x.mantissa}*2^{x.exponent} has {len} significant bits, not 53"
    else if lead ≥ -1022 then
      -- normal: pad `m` up to exactly 53 bits, then drop the implicit leading one
      let frac : UInt64 := (m * 2 ^ (53 - len) : Nat).toUInt64 - (2 ^ 52 : UInt64)
      let biased : UInt64 := (lead + 1023).toNat.toUInt64
      pure ((sign <<< 63) ||| ((biased &&& 0x7FF) <<< 52) ||| frac)
    else if x.exponent < -1074 then
      throw s!"{x.mantissa}*2^{x.exponent} is finer than binary64's smallest subnormal"
    else
      -- subnormal: the fixed exponent `-1074`, no implicit leading bit
      pure ((sign <<< 63) ||| (m * 2 ^ (x.exponent + 1074).toNat : Nat).toUInt64)

def ieee64ToHex (x : IEEE IEEEFormat.binary64) : Except String String :=
  (ieee64ToBits x).map uint64ToHex

def floatToIeeeHex (x : Float) : Except String String := ieee64ToHex (floatToIEEE64 x)

/-- `hex → Float → IEEE .binary64 → hex`, checked on every token of `hexes`: the regression for
`ieee64ToBits` exactly inverting `floatToIEEE64` on binary64's own grid. -/
def checkRoundTrip (hexes : Array String) : Except String Unit :=
  hexes.foldlM (fun _ h => do
    let x ← hexToFloat h
    let h2 ← floatToIeeeHex x
    if h2 = h then pure () else throw s!"round-trip: `{h}` became `{h2}`") ()

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
