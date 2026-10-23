module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Operations.MatPow

@[expose] public section

/-!
# Matrix zonotopes: one order of the exponential's Taylor series

`expMatZonoTerm`: order `i` of [1, Sec. 3.1]'s series as a matrix zonotope: the zonotope's
`i`-th power scaled by `1/i!`.

## Inputs
* `M` – matrix zonotope
* `i` – order

## Output
* matrix zonotope of the order's Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". In A. Rauh and E. Auer (eds.), Modeling, Design, and
      Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Order `i` of the series as a matrix zonotope: the zonotope's `i`-th power
scaled by `1/i!`. -/
noncomputable def MatExp.expMatZonoTerm (M : Zonotope (Mat ℝ n n)) (i : ℕ) :
    Zonotope (Mat ℝ n n) :=
  Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) ((Nat.factorial i : ℝ)⁻¹)) (M.matPow i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
