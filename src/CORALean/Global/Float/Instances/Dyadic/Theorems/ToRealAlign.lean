module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
public import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowAlign

@[expose] public section

/-!
# A dyadic read at any smaller exponent

A dyadic read at any exponent at or below its own, moved there by
`two_zpow_align`. Needed to compare two dyadics: `Order`'s `le` reads both at
the smaller of their two exponents, which this lets it do without changing
either's value.

## Inputs
* `d` – dyadic
* `e` – smaller exponent

## Hypotheses
* `h` – the exponent is at most the dyadic's own

## Conclusion
* the dyadic's value is its mantissa shifted to that exponent times the power of two
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_align (d : Dyadic p) {e : ℤ} (h : e ≤ d.exponent) :
    toReal d = ((d.mantissa * 2 ^ (d.exponent - e).toNat : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal_def]
  push_cast
  rw [mul_assoc, two_zpow_align h]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
