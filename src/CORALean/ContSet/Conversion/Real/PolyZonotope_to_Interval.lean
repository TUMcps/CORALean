import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval

/-!
# A polynomial zonotope as a box

The dependent generators are freed first, then the zonotope's own box. Cheap and
loose in one particular way: the freeing is what costs precision, and the box
that follows is tight for what it is given.

CORA's `interval(polyZonotope)` does better by splitting the dependent
generators on the parity of their exponents — an even monomial reaches only
`[0,1]`, so half its generator can move into the centre. That needs the exponent
matrix, which this route has already thrown away.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def PolyZonotope.interval (PZ : PolyZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  PZ.zonotope.interval

theorem PolyZonotope.interval_outer (PZ : PolyZonotope (Vec ℝ n)) :
    PZ.construct ⊆ PZ.interval.construct :=
  subset_trans PZ.zonotope_outer (Zonotope.interval_outer _)

end CORALean.Real
