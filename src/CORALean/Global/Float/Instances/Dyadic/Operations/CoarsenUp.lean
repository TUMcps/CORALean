module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# Coarsening an operand upward

`exactAdd` aligns both operands to the smaller exponent, and so forms `2 ^ gap`; when an operand
sits billions of binades below the other (`expUp` at a depth above the mantissa width produces
such exponents) the Lean runtime aborts on that power. `coarsenUp e d` rounds `d` up to the grid
of exponent `e` (no change when `d.exponent ≥ e` already) by a bit shift, which is cheap whatever
the gap. For an operand far below the other, this is exactly the nudge past the larger one that
a directed sum needs: one unit at `e`, or nothing. The ceiling is the floor of the negation.
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

def coarsenUp (e : ℤ) (d : Dyadic p) : Dyadic p :=
  ⟨-((-d.mantissa) >>> (e - d.exponent).toNat), max d.exponent e⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
