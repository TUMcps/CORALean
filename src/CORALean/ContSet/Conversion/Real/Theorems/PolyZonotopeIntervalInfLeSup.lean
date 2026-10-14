module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A polynomial zonotope as a box

Two routes, the looser one first. `interval` frees every dependent generator
before boxing — [1, Prop. 2.7] — cheap, and loose in one particular way: the
freeing is what costs precision, the box that follows being tight for what it
is given.

`intervalEven` goes through `zonotopeEven` instead, splitting generators on
their exponents' parity before boxing — [2, Prop. 1], and CORA's own
`interval(polyZonotope)`. Tighter wherever an even-exponent generator exists,
since half of it moves into the centre rather than being boxed whole.

Both boxes come out ordered, which the type does not say: a polynomial
zonotope is never empty, and a box enclosing a point cannot have its `sup`
below its `inf`. Anything reading a box as a radius needs that.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
* [2] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box is ordered, the set having a point for it to enclose. -/
theorem PolyZonotope.interval_inf_le_sup (pZ : PolyZonotope (Vec ℝ n)) (i : Fin n) :
    pZ.interval.inf i ≤ pZ.interval.sup i := by
  have hmem := pZ.interval_contains (pZ.point_mem_construct (a := fun _ => 0)
    fun _ => by rw [abs_zero]; exact zero_le_one)
  exact le_trans (hmem i).1 (hmem i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
