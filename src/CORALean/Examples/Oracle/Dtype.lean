import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Oracle.Codec
import CORALean.Global.Float.Instances.Dyadic.API
import CORALean.Global.Float.Instances.FixedPoint.API
import CORALean.Global.Float.Instances.IEEE.API

/-!
# A dtype, as a bundle of checked-exact operations

`DtypeOps 𝕋` is what an op handler needs of the dtype string beyond
`[FloatOps 𝕋] [SoundFloatArithmetic 𝕋]`: `readExact` for "every input is exactly
representable", `roundToScalar` for `roundTo`'s one exception, `showExact` for a
normalised `"m*2^e"` out. `fixedpoint:<k>`'s values are decimal and generally
not dyadic once rounded (`0.01 + 0.01 = 1/50`), so `showExact` there is instead
`"m*10^e"` (`m` not a multiple of `10`, `"0*10^0"` at zero) -- a documented
grammar extension so every value the oracle prints for `fixedpoint` also
parses back: `Codec.lean`'s `ExactScalar.decNeg` is what `"m*10^e"` at `e < 0`
parses onto; `ieee`/`dyadic` refuse it, not being generally exact in binary.

`roundToScalar`'s `nearest` ties to even: the operand whose own grid mantissa is
even, generalised to the least-significant decimal digit for `fixedpoint`. Both
directed roundings are sound for *any* off-grid input, not only a rounded
operation's own output, so the returned error is exact before it is itself
rounded outward: an informal soundness claim, not a theorem restated here.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Bench

/-- `CORALean.Float.Dyadic`, under its own name: Mathlib's `_root_.Dyadic` otherwise wins
ambiguous resolution, even with `CORALean.Float` open. -/
abbrev DyP (p : Nat) : Type := CORALean.Float.Dyadic p


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `down`/`up`/`down`-or-`up` by `mode`, or an error naming a bad mode -- `pick` breaks a
`nearest` tie, called only then. -/
def aux_pickByMode {α : Type} (mode : String) (down up : α) (pick : Unit → Bool) :
    Except String α :=
  match mode with
  | "down" => pure down
  | "up" => pure up
  | "nearest" => pure (if pick () then down else up)
  | m => throw s!"roundTo: `mode` must be `nearest`, `down` or `up`, not `{m}`"

/-- `x` closer to `down` than to `up`, ties to even -- `down ≤ x ≤ up` is assumed, as every
caller below has it from a pair of sound directed roundings. -/
def aux_pickDown (down up x : ExactDyadic) : Bool :=
  match ExactDyadic.cmp (ExactDyadic.sub x down) (ExactDyadic.sub up x) with
  | .lt => true
  | .gt => false
  | .eq => down.mantissa % 2 = 0

/-- The decimal counterpart: `down`, `up`, `x` aligned to their least common digit count. -/
def aux_pickDownDec (downM upM xM : Int) (downD upD xD : Nat) : Bool :=
  let D := max xD (max downD upD)
  let xs := xM * 10 ^ (D - xD)
  let downs := downM * 10 ^ (D - downD)
  let ups := upM * 10 ^ (D - upD)
  if xs - downs < ups - xs then true else if xs - downs > ups - xs then false else downs % 2 = 0

/-- `x` normalised: `m` not a multiple of `10`, or `"0*10^0"` at zero -- `fixedpoint`'s own
grammar, see the module docstring; a value it prints this way parses back through
`ExactScalar.decNeg` (or `.dy`, once stripping reaches `d = 0`) unchanged. -/
def showFixedPointExact {f : Nat} (x : FixedPoint f) : String :=
  if x.m = 0 then "0*10^0" else
    let (m', d') := strip x.m x.d
    s!"{m'}*10^{-(d' : Int)}"
where
  -- not `aux_`-named: a `where`-local helper, not a file-scope one the convention governs.
  strip (m : Int) (d : Nat) : Int × Nat :=
    if d = 0 then (m, 0) else if m % 10 = 0 then strip (m / 10) (d - 1) else (m, d)


-- ========================================  MAIN TYPE  ========================================= --

/-- What an op handler needs of a dtype beyond `[FloatOps 𝕋] [SoundFloatArithmetic 𝕋]`:
a checked exact reader, `roundTo`'s exact-input rounding, and a normalised printer. -/
structure DtypeOps (𝕋 : Type) [FloatOps 𝕋] where
  label : String
  readExact : String → ExactScalar → Except String 𝕋
  roundToScalar : String → ExactScalar → Except String (𝕋 × 𝕋 × 𝕋)
  showExact : 𝕋 → String

/-- The message every `ieee`/`dyadic` `.decNeg` rejection shares: a negative decimal exponent
is generally not exact in binary, `1/50` again. -/
def aux_decNegRefused (what : String) (m : Int) (d : Nat) : String :=
  s!"{what}: {m}*10^-{d} is a decimal fraction, not exactly representable in binary; \
    only fixedpoint dtypes accept a negative decimal exponent"

/-- `d`, rounded both ways into `IEEE fmt` -- always defined, `IEEE`'s exponent range checked
only afterwards, by the caller. -/
def ieeeRoundPair (fmt : IEEEFormat) (d : ExactDyadic) : IEEE fmt × IEEE fmt :=
  let xg : DyP fmt.p := ⟨d.mantissa, d.exponent⟩
  (IEEE.roundDown (fmt := fmt) xg, IEEE.roundUp (fmt := fmt) xg)

-- `value`, then its own rounding error `d - value`, both checked past `IEEE.overflows`.
def ieeeRoundToScalar (fmt : IEEEFormat) (mode : String) : ExactScalar →
    Except String (IEEE fmt × IEEE fmt × IEEE fmt)
  | .decNeg m d => throw (aux_decNegRefused "roundTo" m d)
  | .dy d => do
    -- `value`, by `mode`; the rounding error, always outward, whichever `value` was kept
    let (down, up) := ieeeRoundPair fmt d
    let value ← aux_pickByMode mode down up
      (fun _ => aux_pickDown ⟨down.mantissa, down.exponent⟩ ⟨up.mantissa, up.exponent⟩ d)
    if IEEE.overflows value then
      throw s!"roundTo: {showExactDyadic d} overflows the format ({fmt.p} bits, emax {fmt.emax})"
    let err := ExactDyadic.sub d ⟨value.mantissa, value.exponent⟩
    let (errDown, errUp) := ieeeRoundPair fmt err
    if IEEE.overflows errDown ∨ IEEE.overflows errUp then
      throw s!"roundTo: the rounding error at {showExactDyadic d} overflows the format \
        ({fmt.p} bits, emax {fmt.emax})"
    pure (value, errDown, errUp)

def ieeeDtypeOps (label : String) (fmt : IEEEFormat) : DtypeOps (IEEE fmt) where
  label := label
  readExact field
    | .dy d => d.toIEEE field fmt
    | .decNeg m d => throw (aux_decNegRefused s!"field `{field}`" m d)
  roundToScalar := ieeeRoundToScalar fmt
  showExact x := showExactDyadic ⟨x.mantissa, x.exponent⟩

-- `Dyadic p`'s own counterpart: unbounded exponent, so no overflow check is ever needed.
def dyadicRoundToScalar (p : Nat) (mode : String) : ExactScalar →
    Except String (DyP p × DyP p × DyP p)
  | .decNeg m d => throw (aux_decNegRefused "roundTo" m d)
  | .dy d => do
    let down : DyP p := CORALean.Float.Dyadic.roundDown ⟨d.mantissa, d.exponent⟩
    let up : DyP p := CORALean.Float.Dyadic.roundUp ⟨d.mantissa, d.exponent⟩
    let value ← aux_pickByMode mode down up
      (fun _ => aux_pickDown ⟨down.mantissa, down.exponent⟩ ⟨up.mantissa, up.exponent⟩ d)
    let err := ExactDyadic.sub d ⟨value.mantissa, value.exponent⟩
    let errG : DyP p := ⟨err.mantissa, err.exponent⟩
    pure (value, CORALean.Float.Dyadic.roundDown errG, CORALean.Float.Dyadic.roundUp errG)

def dyadicDtypeOps (label : String) (p : Nat) : DtypeOps (DyP p) where
  label := label
  readExact field
    | .dy d => d.toDyadicP field p
    | .decNeg m d => throw (aux_decNegRefused s!"field `{field}`" m d)
  roundToScalar := dyadicRoundToScalar p
  showExact x := showExactDyadic ⟨x.mantissa, x.exponent⟩

/-- `v`, at `FixedPoint f`, off-grid but exact -- `.dy` embeds through `ExactDyadic.toFixedPoint`
at enough digits (`fitsDigits`'s own bound), `.decNeg` is already this shape, unconditionally. -/
def aux_toFixedPointExact (f : Nat) : ExactScalar → Except String (FixedPoint f)
  | .decNeg m d => pure ⟨m, d⟩
  | .dy d => do
    -- enough decimal digits for an *exact* embedding of `d`, `fitsDigits`'s own bound
    let d0 := max f (max 0 (-d.exponent)).toNat
    let xExact ← d.toFixedPoint "x" d0
    pure ⟨xExact.m, xExact.d⟩

def fixedPointRoundToScalar (f : Nat) (mode : String) (v : ExactScalar) :
    Except String (FixedPoint f × FixedPoint f × FixedPoint f) := do
  -- `xg` off `f`'s own grid but exact; `down`/`up` are `FixedPoint.roundDown`/`roundUp` of it
  let xg ← aux_toFixedPointExact f v
  let down := FixedPoint.roundDown xg
  let up := FixedPoint.roundUp xg
  let value ← aux_pickByMode mode down up
    (fun _ => aux_pickDownDec down.m up.m xg.m down.d up.d xg.d)
  let d1 := max xg.d value.d
  let em : Int := xg.m * 10 ^ (d1 - xg.d) - value.m * 10 ^ (d1 - value.d)
  let errG : FixedPoint f := ⟨em, d1⟩
  pure (value, FixedPoint.roundDown errG, FixedPoint.roundUp errG)

def fixedPointDtypeOps (label : String) (f : Nat) : DtypeOps (FixedPoint f) where
  label := label
  readExact field
    | .dy d => d.toFixedPoint field f
    | .decNeg m d =>
      if d ≤ f then pure (⟨m * 10 ^ (f - d), f⟩ : FixedPoint f)
      else throw s!"field `{field}`: {m}*10^-{d} needs more than {f} decimal digits"
  roundToScalar := fixedPointRoundToScalar f
  showExact := showFixedPointExact

/-- Every valid `dtype` form, for `ping` and for an unknown-dtype error. -/
def dtypeForms : List String :=
  [ "binary64", "ieee:binary64", "ieee:binary32", "ieee:binary16", "ieee:binary8", "ieee:binary4",
    "dyadic:<p>", "fixedpoint:<k>" ]

/-- `dtypeStr`, resolved onto a scalar `𝕋` and its `DtypeOps`, handed to `k` -- the one place a
dtype string becomes a type. `binary64` is `ieee:binary64`'s alias, the axiom-free `IEEE`
instance, never hardware `Float`. -/
def withDtype {α : Type} (dtypeStr : String)
    (k : {𝕋 : Type} → [FloatOps 𝕋] → [SoundFloatArithmetic 𝕋] → [ToRat 𝕋] →
      DtypeOps 𝕋 → Except String α) :
    Except String α :=
  -- one arm per `dtypeForms` entry; `dyadic:`/`fixedpoint:` parse their own suffix
  match dtypeStr with
  | "binary64" | "ieee:binary64" =>
    k (𝕋 := IEEE .binary64) (ieeeDtypeOps "ieee:binary64" .binary64)
  | "ieee:binary32" => k (𝕋 := IEEE .binary32) (ieeeDtypeOps "ieee:binary32" .binary32)
  | "ieee:binary16" => k (𝕋 := IEEE .binary16) (ieeeDtypeOps "ieee:binary16" .binary16)
  | "ieee:binary8" => k (𝕋 := IEEE .e4m3) (ieeeDtypeOps "ieee:binary8" .e4m3)
  | "ieee:binary4" => k (𝕋 := IEEE .e2m1) (ieeeDtypeOps "ieee:binary4" .e2m1)
  | s =>
    if s.startsWith "dyadic:" then
      match (s.drop 7).toNat? with
      | some p => k (𝕋 := DyP p) (dyadicDtypeOps s p)
      | none => throw s!"dtype `{s}`: `dyadic:<p>` needs a natural-number precision"
    else if s.startsWith "fixedpoint:" then
      match (s.drop 11).toNat? with
      | some f => k (𝕋 := FixedPoint f) (fixedPointDtypeOps s f)
      | none => throw s!"dtype `{s}`: `fixedpoint:<k>` needs a natural-number digit count"
    else
      throw s!"unknown dtype `{s}` -- valid forms: {String.intercalate ", " dtypeForms}"

/-- What resolves a `dtype` string onto a scalar and hands it to `k`: `withDtype`, or one that
knows more dtypes. -/
abbrev Resolver : Type 1 :=
  {α : Type} → String → ({𝕋 : Type} → [FloatOps 𝕋] → [SoundFloatArithmetic 𝕋] → [ToRat 𝕋] →
    DtypeOps 𝕋 → Except String α) → Except String α

/-- The dtypes an oracle executable serves: their names, for `ping`, and their resolver. -/
structure DtypeSet where
  forms : List String
  resolve : Resolver

/-- The dtypes of `lake exe oracle`. -/
def sounds : DtypeSet := ⟨dtypeForms, withDtype⟩

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
