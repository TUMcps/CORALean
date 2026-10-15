module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# The formats of IEEE 754 and OCP MX: the representation

`IEEE fmt` is `mantissa * 2 ^ exponent`, as `Dyadic` is, and every rounded operation lands on the
finite grid of `fmt`: `p` significand bits, and never a step finer than the smallest subnormal,
`2 ^ qmin`. On every value in range that is IEEE 754's round-toward-±∞, subnormals included.

The exponent stays unbounded, so a value past `maxFinite` is representable here where the format
would hold `±∞` or saturate. `overflows` detects it, and the bench reports a run as overflowed
from the first step that stores one: values beyond the format's range are detected and reported
as overflow, never silently continued.

`half` alone leaves the grid: it only lowers the exponent, so it is exact, as the class demands,
and below the smallest subnormal its result is finer than any number of `fmt`. The next rounded
operation rounds it back. Nothing else departs from the format, and `toReal` is `Dyadic`'s,
through `toDyadic`, so the exact steps and their proofs are `Dyadic`'s too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

/-- A binary format's finite numbers: `p` significand bits counting the implicit one, normal
exponents `emin` to `emax`, and `maxSignificand * 2 ^ (emax - p + 1)` the largest value, below
`(2 ^ p - 1) * 2 ^ (emax - p + 1)` where a format spends its top codes on NaN. -/
structure IEEEFormat where
  p : ℕ
  emin : ℤ
  emax : ℤ
  maxSignificand : ℕ
deriving Repr, DecidableEq

namespace IEEEFormat

/-- IEEE 754-2019 binary64, Table 3.5: `p = 53`, `emax = 1023`, `emin = 1 - emax` (Sec. 3.3). -/
def binary64 : IEEEFormat := ⟨53, -1022, 1023, 2 ^ 53 - 1⟩

/-- IEEE 754-2019 binary32, Table 3.5: `p = 24`, `emax = 127`, `emin = -126`. -/
def binary32 : IEEEFormat := ⟨24, -126, 127, 2 ^ 24 - 1⟩

/-- IEEE 754-2019 binary16, Table 3.5: `p = 11`, `emax = 15`, `emin = -14`; the largest value is
`2047 * 2 ^ 5 = 65504` and the smallest subnormal `2 ^ -24`. -/
def binary16 : IEEEFormat := ⟨11, -14, 15, 2 ^ 11 - 1⟩

/-- OCP Microscaling Formats (MX) v1.0, FP8 E4M3: bias 7, `emin = -6`, `emax = 8`, largest
`1.75 * 2 ^ 8 = 448` (`S.1111.111` is NaN), smallest subnormal `2 ^ -9`, no infinities. -/
def e4m3 : IEEEFormat := ⟨4, -6, 8, 14⟩

/-- OCP Microscaling Formats (MX) v1.0, FP4 E2M1: bias 1, `emin = 0`, `emax = 2`, largest
`1.5 * 2 ^ 2 = 6`, no infinities or NaN: `0, 0.5, 1, 1.5, 2, 3, 4, 6` and their negations. -/
def e2m1 : IEEEFormat := ⟨2, 0, 2, 3⟩

/-- The exponent of the smallest subnormal, which is the finest step of the grid. -/
def qmin (fmt : IEEEFormat) : ℤ := fmt.emin - fmt.p + 1

/-- The largest finite value, exactly. -/
def maxFinite (fmt : IEEEFormat) : ℚ := fmt.maxSignificand * 2 ^ (fmt.emax - fmt.p + 1)

end IEEEFormat


-- ========================================  MAIN TYPE  ========================================= --

/-- A number in format `fmt`. The fields are `Dyadic`'s and unconstrained: `fmt` fixes the grid
the rounded operations land on, which `half` and an exact input may leave until the next one. -/
structure IEEE (fmt : IEEEFormat) where
  mantissa : ℤ
  exponent : ℤ

namespace IEEE

variable {fmt : IEEEFormat}

/-- The same pair at `fmt`'s precision, which is where every exact step is taken. -/
def toDyadic (x : IEEE fmt) : Dyadic fmt.p := ⟨x.mantissa, x.exponent⟩

/-- `Dyadic.toReal`, and computable for the same reason. -/
def toReal (x : IEEE fmt) : ℝ := x.toDyadic.toReal

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
