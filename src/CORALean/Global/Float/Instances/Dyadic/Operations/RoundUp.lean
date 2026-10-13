module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Shift

@[expose] public section

/-!
# Rounding a mantissa up to `p` bits

The ceiling is the floor of the negation, so this negates, shifts right by
`shift` bits, and negates back.
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

def roundUp (d : Dyadic p) : Dyadic p :=
  ⟨-(-d.mantissa / 2 ^ d.shift), d.exponent + d.shift⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
