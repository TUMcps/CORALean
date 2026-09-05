import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# A polynomial zonotope as a box

The dependent generators are freed first, then the zonotope's own box. Cheap and
loose in one particular way: the freeing is what costs precision, and the box
that follows is tight for what it is given.

CORA's `interval(polyZonotope)` does better by splitting the dependent
generators on the parity of their exponents — an even monomial reaches only
`[0,1]`, so half its generator can move into the centre. That needs the exponent
matrix, which this route has already thrown away.

The box that comes out is always ordered, which the type does not say: a
polynomial zonotope is never empty, and a box enclosing a point cannot have its
`sup` below its `inf`. Anything reading the box as a radius needs that.
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

/-- The box is ordered, the set having a point for it to enclose. -/
theorem PolyZonotope.interval_inf_le_sup (PZ : PolyZonotope (Vec ℝ n)) (i : Fin n) :
    PZ.interval.inf i ≤ PZ.interval.sup i := by
  have hmem := PZ.interval_outer (PZ.point_mem_construct (a := fun _ => 0)
    fun _ => by rw [abs_zero]; exact zero_le_one)
  exact le_trans (hmem i).1 (hmem i).2

end CORALean.Real
