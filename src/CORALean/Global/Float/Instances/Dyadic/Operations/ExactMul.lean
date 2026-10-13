import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# The exact product

Closed on dyadics, so this loses nothing; only the mantissa grows, to `2p`
bits at a `p`-bit product. `MulUp`/`MulDown` round it back down to `p`.
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

def exactMul (a b : Dyadic p) : Dyadic p :=
  ⟨a.mantissa * b.mantissa, a.exponent + b.exponent⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
