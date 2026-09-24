import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# Matrix zonotopes: enclosing the exponential of a matrix zonotope

`expMatZonoEnclosure`: CORA's `expmInd` at [1, Sec. 3.3.2], which is what `expm` defers to:
the finite Taylor sum kept as a matrix zonotope, and the tail bounded through the interval
matrix the zonotope
encloses, where no matrix-zonotope machinery is needed at all. The remainder is a box of one
uniform width — `expRemainderBound` bounds a norm, not an entry — and becomes a matrix
zonotope with one generator per entry.

The order `η` is a choice, sound at any value: `expRemainderBound` widens to
cover whatever the sum left out.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor sum kept as a matrix zonotope, widened by the tail bound taken at
the dominating matrix of the interval matrix the zonotope encloses. -/
noncomputable def MatExp.expMatZonoEnclosure (M : Zonotope (Mat ℝ n n)) (η : ℕ) :
    Zonotope (Mat ℝ n n) :=
  Zonotope.plus (MatExp.expMatZonoTaylor M η)
    (MatExp.expMatZonoRemainder n (MatExp.expRemainderBound M.interval.absMax η))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
