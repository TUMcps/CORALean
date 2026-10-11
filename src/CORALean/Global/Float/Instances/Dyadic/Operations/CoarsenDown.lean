import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# Coarsening an operand downward

The mirror image of `coarsenUp`: `d` rounded down to the grid of exponent `e` by a bit shift,
the floor of the mantissa at the raised exponent.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def coarsenDown (e : ℤ) (d : Dyadic p) : Dyadic p :=
  ⟨d.mantissa >>> (e - d.exponent).toNat, max d.exponent e⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
