import CORALean.Examples.HardwareCheck.Exact

/-!
# The generator and the input cases

SplitMix64, so a seed reproduces a run on every platform, and the inputs `hardwarecheck` feeds
every operation: uniform bit patterns and structured ones, aimed at the places the axioms could
fail -- zeros, subnormals, the ends of the normal range, ties, cancellation, `1 ± ulp`, operands
about `2 ^ 53` apart, and products and quotients landing on either end of the range.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.HardwareCheck


-- ========================================  MAIN TYPE  ========================================= --

/-- SplitMix64's state. -/
structure Rng where
  s : UInt64


def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Uniform in `[0, k)`, up to a modulo bias no test here can see. -/
def Rng.below (g : Rng) (k : Nat) : Nat × Rng :=
  let (u, g) := g.next
  (u.toNat % k, g)

/-- Sign, biased exponent field, fraction. -/
def mkBits (sign : Bool) (e : Nat) (frac : UInt64) : UInt64 :=
  let s : UInt64 := if sign then 1 else 0
  (s <<< 63) ||| ((e.toUInt64 &&& 0x7FF) <<< 52) ||| (frac &&& 0xFFFFFFFFFFFFF)

def expOf (b : UInt64) : Nat := ((b >>> 52) &&& 0x7FF).toNat

def clampExp (e : Int) : Nat := (max 1 (min 2046 e)).toNat

/-- Whether the bits are a finite binary64. -/
def isFin (b : UInt64) : Bool := expOf b != 0x7FF

/-- The values every pair of which is tried: zeros, subnormals, the ends of the normal range,
`1 ± ulp` and their neighbours, both signs. -/
def specials : Array UInt64 :=
  let pos : Array UInt64 := #[0, 1, 2, 3, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
    0x0010000000000001, 0x7FEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFE, 0x7FE0000000000000,
    0x3FF0000000000000, 0x3FF0000000000001,
    0x3FEFFFFFFFFFFFFF, 0x3FE0000000000000, 0x4000000000000000, 0x4008000000000000,
    0x3FB999999999999A, 0x4340000000000000, 0x4340000000000001, 0x3CA0000000000000,
    0x1FF0000000000000, 0x5FF0000000000000, 0x2000000000000000, 0x5FE0000000000000,
    0x0180000000000000, 0x7FD0000000000000]
  pos ++ pos.map (· ||| 0x8000000000000000)

/-- Non-finite inputs. -/
def nonFinite : Array UInt64 :=
  #[0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0xFFF8000000000000,
    0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF]

/-- Finite values to pair them with. -/
def finiteProbe : Array UInt64 :=
  #[0, 0x8000000000000000, 1, 0x3FF0000000000000, 0xBFF0000000000000, 0x7FEFFFFFFFFFFFFF]

/-- One random pair, of the `k`-th kind. -/
def pairOf (k : Nat) (g : Rng) : (UInt64 × UInt64) × Rng :=
  let (a, g) := g.next
  let (u, g) := g.next
  let (v, g) := g.next
  let sa := a >>> 63 == 1
  let sb := u >>> 63 == 1
  let ea := expOf a
  match k % 9 with
  | 0 => ((a, u), g)
  | 1 => -- exponent of `b` within 60 of `a`'s: operands about `2 ^ 53` apart among them
    ((a, mkBits sb (clampExp (ea + (v % 121).toNat - 60)) u), g)
  | 2 => -- ties: `b` half an ulp of `a` (or a nearby power of two below it)
    let frac := if v % 5 == 0 then u else 0
    ((mkBits sa (clampExp ea) a, mkBits sb (clampExp (ea - 52 - (v % 3).toNat)) frac), g)
  | 3 => -- cancellation: `a` and `-a`, up to a bit
    let d : UInt64 := if v % 3 == 0 then 0 else if v % 3 == 1 then 1 else 0 - 1
    ((a, (a ^^^ 0x8000000000000000) + d), g)
  | 4 => -- products landing on either end of the range
    let t : Int := [0, 1, 2, 3, 2044, 2045, 2046, 2047, 2048].getD (v % 9).toNat 0
    ((a, mkBits sb (clampExp (t + 1023 - ea)) u), g)
  | 5 => -- quotients landing on either end of the range
    let t : Int := [0, 1, 2, 3, 2044, 2045, 2046, 2047, 2048].getD (v % 9).toNat 0
    ((a, mkBits sb (clampExp (ea + 1023 - t)) u), g)
  | 6 => ((a, mkBits sb (1020 + (v % 7).toNat) u), g)
  | 7 => -- subnormal and tiny
    ((mkBits sa (v % 4).toNat a, mkBits sb ((v >>> 8) % 4).toNat u), g)
  | _ => -- both near the top of the range
    ((mkBits sa (2040 + (v % 7).toNat) a, mkBits sb (2040 + ((v >>> 8) % 7).toNat) u), g)

end CORALean.HardwareCheck


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
