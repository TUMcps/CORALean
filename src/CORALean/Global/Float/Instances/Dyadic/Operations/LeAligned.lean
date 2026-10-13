module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# Comparison by aligning

Aligned to the smaller exponent, where both mantissas are integers. Forms `2 ^ gap`, so it is
the specification of `le` rather than what runs: `le` agrees with it (`le_iff`) but does not
abort on a huge gap.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def leAligned (a b : Dyadic p) : Bool :=
  a.mantissa * 2 ^ (a.exponent - min a.exponent b.exponent).toNat ≤
    b.mantissa * 2 ^ (b.exponent - min a.exponent b.exponent).toNat

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
