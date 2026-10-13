import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.Rational
import CORALean.Global.Float.Instances.IEEE.API

/-!
# `--type ieee`: the formats, and reading a config into one

`--format` names the format, with the harness's own five labels: `binary64`, `binary32` and
`binary16` are IEEE 754-2019's, `binary8` is OCP MX E4M3 and `binary4` OCP MX E2M1. A config
leaf must be a number of the format -- `p` bits, no finer than the smallest subnormal, no larger
than the largest finite value -- and is rejected rather than rounded otherwise, as `Dyadic`'s
`toDyadicP` rejects one over `p` bits: rounding `A` or `dt` would analyse another system.

`ieeeNumberType` is what `meta` records: the format's parameters, and `IEEE.overflows`, from
which the writers find the first step that stores a value past the format's range.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float
open Lean (Json)

/-- The five `--format` labels, as formats. -/
def ieeeFormat : String → Except String IEEEFormat
  | "binary64" => pure .binary64
  | "binary32" => pure .binary32
  | "binary16" => pure .binary16
  | "binary8" => pure .e4m3
  | "binary4" => pure .e2m1
  | fmt => throw s!"`--format` is one of binary64|binary32|binary16|binary8|binary4, not `{fmt}`"

/-- The name `meta.number_type` gives a format. -/
def ieeeName (label : String) : String :=
  match label with
  | "binary8" => "ieee E4M3 (OCP MX)"
  | "binary4" => "ieee E2M1 (OCP MX)"
  | _ => s!"ieee {label}"

/-- `d` at `IEEE fmt`, exactly, off the grid or not -- for a computed quantity, which the first
rounded operation applied to it rounds onto the grid, as `toDyadicPUnchecked` is for `Dyadic`. -/
def ExactDyadic.toIEEEUnchecked {fmt : IEEEFormat} (d : ExactDyadic) : IEEE fmt :=
  ⟨d.mantissa, d.exponent⟩

/-- `d` at `IEEE fmt` if it is a number of the format, else an error naming the field. -/
def ExactDyadic.toIEEE (field : String) (fmt : IEEEFormat) (d : ExactDyadic) :
    Except String (IEEE fmt) :=
  let x : IEEE fmt := d.toIEEEUnchecked
  if !fitsPrecision fmt.p d then
    throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more than {fmt.p} bits"
  else if d.mantissa ≠ 0 && d.exponent < fmt.qmin then
    throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} is finer than the smallest \
      subnormal 2^{fmt.qmin}, not a number of the format"
  else if IEEE.overflows x then
    throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} exceeds the largest finite \
      value {fmt.maxFinite}"
  else pure x

/-- The nearest double, for the output's `double` fields, as `dyadicToFloatApprox` is. -/
def ieeeToFloatApprox {fmt : IEEEFormat} (x : IEEE fmt) : Float :=
  dyadicToFloatApprox x.toDyadic


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `meta`'s description, the format's parameters, and the overflow check. -/
def ieeeNumberType (label : String) (fmt : IEEEFormat) : NumberType (IEEE fmt) where
  description := ieeeName label
  overflows := some IEEE.overflows
  params :=
    [ ("ieee_format", Json.mkObj
        [ ("p", Lean.toJson fmt.p), ("emin", Lean.toJson fmt.emin),
          ("emax", Lean.toJson fmt.emax),
          ("max_finite", Json.str s!"{fmt.maxSignificand}*2^{fmt.emax - fmt.p + 1}"),
          ("min_subnormal", Json.str s!"2^{fmt.qmin}") ]) ]

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
