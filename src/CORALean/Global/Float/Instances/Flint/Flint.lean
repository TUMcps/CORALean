import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# FLINT-rounded dyadics: the representation

`Flint p` is `mantissa * 2 ^ exponent`, the same pair `Dyadic p` holds and read
the same way: `toReal` is `Dyadic.toReal` of that pair, an ordinary definition,
so everything exact about a `Flint` value is proved exactly as it is for
`Dyadic`. What differs is who rounds. The six directed operations are handed to
FLINT's `arf_add`/`arf_mul`/`arf_div` at `p` bits, compiled C that Lean cannot
see into, so their directions are assumed once, in `Definitions/Axioms`, not
proved.

The exponent is unbounded on both sides of the boundary, FLINT's being an
`fmpz`, so nothing overflows or underflows, and the one assumption needs no
range side condition, unlike the hardware's. Opt-in: nothing in the default
build links FLINT (README, "FLINT backend (optional)").
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- `Inhabited` because an `opaque` operation needs a value to stand for. -/
structure Flint (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ
deriving Inhabited

/-- The same pair, read as a `Dyadic`: how every exact fact is borrowed. -/
def Flint.toDyadic {p : ℕ} (a : Flint p) : Dyadic p := ⟨a.mantissa, a.exponent⟩

/-- Computable for the reason `Dyadic.toReal` is, being that very function. -/
def Flint.toReal {p : ℕ} (a : Flint p) : ℝ := a.toDyadic.toReal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
