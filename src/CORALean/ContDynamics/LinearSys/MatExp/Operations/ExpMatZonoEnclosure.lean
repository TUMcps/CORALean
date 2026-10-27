module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# Matrix zonotopes: enclosing the exponential of a matrix zonotope

`expMatZonoEnclosure`: CORA's `expmInd`, the enclosure of [1, Sec. 3.1] at a matrix zonotope with
every order evaluated independently, which is what `expm` defers to: the
finite Taylor sum kept as a matrix zonotope, and the tail bounded through the interval matrix the
zonotope encloses, where no matrix-zonotope machinery is needed. The remainder is a box of one
uniform width (`expRemainderBound` bounds a norm, not an entry) and becomes a matrix zonotope
with one generator per entry. The order `η` is a choice, sound at any value: `expRemainderBound`
widens to cover whatever the sum left out.

## Inputs
* `M` – matrix zonotope
* `η` – Taylor order

## Output
* matrix zonotope enclosing the exponential

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
