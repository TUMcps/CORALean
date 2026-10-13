module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# The exact sum

Closed on dyadics, so this loses nothing; only the mantissa grows, aligned to
the smaller exponent, where both mantissas are integers. `AddUp`/`AddDown`
round it back to `p` bits.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Aligned to the smaller exponent, where both mantissas are integers. -/
def exactAdd (a b : Dyadic p) : Dyadic p :=
  let e := min a.exponent b.exponent
  ⟨a.mantissa * 2 ^ (a.exponent - e).toNat + b.mantissa * 2 ^ (b.exponent - e).toNat, e⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
