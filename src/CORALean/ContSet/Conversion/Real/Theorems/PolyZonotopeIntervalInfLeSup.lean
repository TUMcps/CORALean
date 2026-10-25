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

Two routes, the looser one first. `interval` frees every dependent generator before boxing
([1, Prop. 2.7]): cheap, and loose in one way, the freeing costing the precision. `intervalEven`
goes through `zonotopeEven`, splitting generators on their exponents' parity before boxing
([2, Prop. 1]), and is CORA's own `interval(polyZonotope)`; tighter wherever an even-exponent
generator exists, since half of it moves into the center. Both boxes come out ordered, which the
type does not say: a polynomial zonotope is never empty, and a box enclosing a point cannot have its
`sup` below its `inf`. Anything reading a box as a radius needs that.

## Inputs
* `pZ` – polynomial zonotope
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* lower end of the interval is below its upper end

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
* [2] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
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
