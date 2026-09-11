import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# A polynomial zonotope as a box

The construction is [1, Prop. 2.7].

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

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

def PolyZonotope.interval (pZ : PolyZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  pZ.zonotope.interval

theorem PolyZonotope.interval_contains (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.interval.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.interval_contains _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box is ordered, the set having a point for it to enclose. -/
theorem PolyZonotope.interval_inf_le_sup (pZ : PolyZonotope (Vec ℝ n)) (i : Fin n) :
    pZ.interval.inf i ≤ pZ.interval.sup i := by
  have hmem := pZ.interval_contains (pZ.point_mem_construct (a := fun _ => 0)
    fun _ => by rw [abs_zero]; exact zero_le_one)
  exact le_trans (hmem i).1 (hmem i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
