module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Decimal fixed-point numbers at a target precision: the representation

`FixedPoint f` is `mantissa · 10 ^ (-digits)` with `digits` carried on the
*value*, not fixed by the type: `f` names the digit count a rounded operation
returns to, not a bound every value obeys. Cutting a decimal off after `f`
fractional digits — CORA's `123.4567 → 123.45` — is floor for a positive value
and ceiling for a negative one, so on its own it is not sound; every rounded
operation here floors or ceils explicitly. `digits` only grows through `half`,
one digit at a time; every other rounded operation cuts back to `f`, so a value
returned by `addUp`/`mulDown`/`divUp` and friends is always at exactly `f`
digits again.

`toReal` takes its power of ten through ℚ rather than ℝ directly, the same
detour `Dyadic.toReal` takes and for the same reason: ℚ's division and `pow`
are computable where ℝ's are not, and a noncomputable `toReal` would make every
generic algorithm run at this scalar noncomputable too. `toReal_def` is the
number it denotes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- `m · 10 ^ (-d)`: `f` is the digit count a rounded operation targets, not a
bound `m`/`d` obey -- `d` is stored per value and normally equals `f`. -/
structure FixedPoint (f : ℕ) where
  m : ℤ
  d : ℕ

def FixedPoint.toReal {f : ℕ} (x : FixedPoint f) : ℝ := (((x.m : ℚ) / 10 ^ x.d : ℚ) : ℝ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
